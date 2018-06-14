(* some simple static analyses to learn stuff about the ast *)
open CCOpt.Infix
open Name.Infix

module S = Types.Sub
module E = Types.Environment
module C = Types.Constraint
module A = AST

let rational = Types.Base Types.Rational
let boolean = Types.Base Types.Boolean

(* we build up type inference in the bi-directional sense *)
(* this computes the judgement G |- e -> t *)
let rec infer (env : E.t) (e : A.expr) : Types.t option = match e with
  (* literals always synthesize their own type, which we can infer statically *)
  | A.Literal l -> begin match l with
      | A.Rational _ -> Some rational
      | A.Boolean _ -> Some boolean
    end
  (* identifiers synthesize whatever type they have in the context *)
  | A.Identifier i -> begin match i with
      | A.Var n -> begin match E.get_type n env with
          | Some t -> Some t
          | None -> Some (Types.Variable (n <+ "type"))
        end
      (* although we have to treat indexed variables more like functions *)
      | A.IndexedVar (n, i) ->
        match E.get_type n env with
          | Some (Types.Indexed (d, c)) -> if check env i c then Some d else None
          | _ -> None
    end
  | A.FunCall (f, args) -> 
    let op = match Operation.find_op f with
      | Some op -> op
      | None -> Operation.mk_op f (CCList.length args) in
    begin match op.Operation.signature with
      | Types.Function (xs, x) ->
        if CCList.for_all (fun (e, t) -> check env e t) (CCList.combine args xs) then Some x else None
      | _ -> None
    end
(* and this computes the judgement G |- e <- t *)
and check (env : E.t) (e : A.expr) (t : Types.t) : bool =
  (* case 1 : equality *)
  (* actually pretty much the only case *)
  (* note this thing doesn't really know what to do with vars, aka only works on ground types *)
  match infer env e with
    | Some t' -> t = t'
    | None -> false

(* now, given a type and an expression, we want to build the constrainst C s.t. *)
(* for any G |= C, G |- e <- t *)
open C.Infix
exception TypeMismatch of string

(* this mirros infer above, but anytime there's a call to check we generate a constraint *)
let rec type_constraints (e : A.expr) : Types.t * C.t = match e with
  | A.Literal l -> begin match l with
      | A.Rational _ -> (rational, C.top)
      | A.Boolean _ -> (boolean, C.top)
    end
  | A.Identifier i -> begin match i with
      | A.Var n ->
        let a = Types.Variable (n <+ "type") in
        (a, C.top)
      | A.IndexedVar (n, i) ->
        let a = Types.Variable (n <+ "type") in
        let codom = Types.Variable (n <+ "codom") in
        let dom = Types.Variable (n <+ "dom") in
        let (t, c) = type_constraints i in
          (dom, (codom =:= t) <&> (a =:= Types.Indexed (dom, codom)))
      end
    | A.FunCall (f, args) -> 
      let op = match Operation.find_op f with
        | Some op -> op
        | None -> Operation.mk_op f (CCList.length args) in
      begin match op.Operation.signature with
        | Types.Function (xs, x) ->
          let (at, ac) = CCList.split @@ CCList.map type_constraints args in
          let eq_c = try
            CCList.map2 (=:=) at xs
            with Invalid_argument _ ->
              let f' = Name.to_string f in
              let err = TypeMismatch (f' ^ " has incorrect arity") in
                raise err
          in (x, CCList.flatten (ac @ eq_c))
        | _ ->
          let f' = Name.to_string f in
          let err = TypeMismatch (f' ^ " has non-function type") in
            raise err
      end

(* we now have all the tools we need to infer the desired info about variables *)
let id_to_name : A.id -> Name.t = function
  | A.Var n -> n
  | A.IndexedVar (n, _) -> n

let rec vars_in_expr : A.expr -> Name.t list = function
  | A.Literal _ -> []
  | A.Identifier i -> [id_to_name i]
  | A.FunCall (_, args) -> CCList.flat_map vars_in_expr args

let rec modified_variables : A.t -> Name.t list = function
  | A.Block xs -> CCList.flat_map modified_variables xs
  | A.Assign (i, _) -> [id_to_name i]
  | A.Draw (i, _) -> [id_to_name i]
  | A.ITE (b, l, r) -> (modified_variables l) @ (modified_variables r)
  | A.While (b, e) -> modified_variables e

let rec variables : A.t -> Name.t list = function
  | A.Block xs -> CCList.flat_map variables xs
  | A.Assign (i, e) -> (id_to_name i) :: (vars_in_expr e)
  | A.Draw (i, e) -> (id_to_name i) :: (vars_in_expr e)
  | A.ITE (b, l, r) ->
    (vars_in_expr b) @ (variables l) @ (variables r)
  | A.While (b, e) ->
    (vars_in_expr b) @ (variables e)

let input_variables : A.t -> Name.t list = fun ast ->
  let modified = modified_variables ast in
  let untouched = CCList.filter (fun n -> not (List.mem n modified)) (variables ast) in
    CCList.sort_uniq (Name.compare) untouched

(* combining constraints over an entire program *)
let rec global_constraints : A.t -> C.t = function
  | A.Block xs -> CCList.flatten @@ CCList.map global_constraints xs
  | A.Assign (i, e) -> 
    let (et, ec) = type_constraints e in
    let (it, ic) = type_constraints (A.Identifier i) in
      (et =:= it) <&> ec <&> ic
  | A.Draw (i, e) ->
    let (et, ec) = type_constraints e in
    let (it, ic) = type_constraints (A.Identifier i) in
      (et =:= it) <&> ec <&> ic
  | A.ITE (b, l, r) ->
    let (bt, bc) = type_constraints b in
    let lc = global_constraints l in
    let rc = global_constraints r in
      (bt =:= boolean) <&> lc <&> rc
  | A.While (b, e) ->
    let (bt, bc) = type_constraints b in
    let ec = global_constraints e in
      (bt =:= boolean) <&> ec <&> bc

let global_context : A.program -> E.t option = fun prog -> 
  let pre, ast, post = prog in
  let ast_constraints = global_constraints ast in
  let pre_constraints = snd (type_constraints pre) in
  let post_constraints = snd (type_constraints post) in
  ast_constraints @ pre_constraints @ post_constraints
    |> C.resolve
    >>= (fun sub ->
      CCList.fold_left (fun e -> fun v ->
        let t = S.get (v <+ "type") sub in
          CCOpt.map2 (E.update v) t e)
      (Some E.empty)
      (CCList.sort_uniq Name.compare (variables ast))
    )

(* for expressions only *)
let expression_context : A.expr -> E.t option = fun ex -> ex
  |> type_constraints
  |> snd
  |> C.resolve
  >>= (fun sub ->
    CCList.fold_left (fun e -> fun v ->
      let t = S.get (v <+ "type") sub in
        CCOpt.map2 (E.update v) t e)
    (Some E.empty)
    (CCList.sort_uniq Name.compare (vars_in_expr ex))
  )