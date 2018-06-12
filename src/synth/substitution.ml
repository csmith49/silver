(* aliasing for ease of use *)
type expr = AST.expr
type id = AST.id

(* we need to be able to use ids as keys *)
module Id = struct
  type t = id

  let compare = Pervasives.compare
end

module IdMap = CCMap.Make(Id)

(* substitutions map ids to exprs *)
type t = expr IdMap.t

(* basic construction just wraps idmap construction *)
let empty : t = IdMap.empty

let singleton : id -> expr -> t = IdMap.singleton

(* more complicated constructor *)
let of_list : (id * expr) list -> t = IdMap.of_list

(* accessor also just wrapped *)
let get : id -> t -> expr option = IdMap.get

(* adding a k, v pair can fail if the v is already defined and not equal *)
let add (k : id) (v : expr) (s : t) : t option =
  match get k s with
    | Some v' when v = v' -> Some s
    | None -> Some (IdMap.add k v s)
    | _ -> None

(* merging, just like adding, can fail *)
let merge (left : t) (right : t) : t option =
  let f = fun ss -> fun (k, v) ->
    match ss with
      | Some s -> add k v s
      | None -> None
  in CCList.fold_left f (Some right) (IdMap.to_list left)

(* because ccopt only lets us map one-param functions *)
let merge_opt (left : t option) (right : t option) : t option =
  match left, right with
    | Some left, Some right -> merge left right
    | _ -> None

(* modifying an expr non-recursively *)
let rec apply (e : expr) (s : t) : expr = match e with
  | AST.Literal _ -> e
  | AST.Identifier i -> IdMap.get_or ~default:e i s
  | AST.BinaryOp (o, l, r) -> AST.BinaryOp (o, apply l s, apply r s)
  | AST.UnaryOp (o, e) -> AST.UnaryOp (o, apply e s)
  | AST.FunCall (f, args) -> AST.FunCall (f, CCList.map (fun e -> apply e s) args)

(* if possible, generate a t that when applied to the left, matches the right *)
let rec left_unify (pattern : expr) (term : expr) : t option =
  if (AST.compare pattern term) = 0 then Some empty else match pattern, term with
    | AST.Identifier i, _ -> Some (singleton i term)
    | AST.BinaryOp (o, l, r), AST.BinaryOp (o', l', r') when Operation.equivalent o o' ->
      merge_opt (left_unify l l') (left_unify r r')
    | AST.UnaryOp (o, e), AST.UnaryOp (o', e') when Operation.equivalent o o' -> left_unify e e'
    | AST.FunCall (f, args), AST.FunCall (f', args') when Operation.equivalent f f' ->
      CCList.fold_left merge_opt (Some empty) (CCList.map2 left_unify args args')
    | _ -> None

(* utility for encoding a lot later *)
let template (values : (string * expr) list) (pattern : string) : expr =
  let e = Parse.parse_expr pattern in
  let s = values
    |> CCList.map (fun (k, v) -> (AST.Var (Name.of_string k), v))
    |> of_list in
  apply e s