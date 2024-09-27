(* we'll end up doing some direct manipulation of formulae *)
module S = SMT.Default

(* an interpolant is just a constraint - we maintain our ast and the logical encoding *)
type t = AST.expr

(* induction manipulation *)
module Induction = struct
  let bound (x : AST.id) (l : AST.expr) (r : AST.expr) : AST.expr =
    let x' = AST.Identifier x in
    let int_restriction = AST.FunCall(Name.of_string "isint", [x']) in
      AST.Infix.(int_restriction &@ (x' >=@ l) &@ (x' <=@ r))

  (* convert pieces of a universally-qauntified formula to a weak form *)
  let weak_induction_form (var : AST.id) (x : AST.id) (l : AST.expr) (r : AST.expr) (e : AST.expr) : AST.expr =
    let i = AST.Identifier var in
    let sub = Substitution.singleton x i in
    let e' = Substitution.apply e sub in
    let bound = bound var l r in
      AST.Infix.(bound =>@ e')

  (* replace universal quantifier with freshest inductive case *)
  let simplify_succ_interpolant : t -> t = function
    | AST.FunCall (f, [AST.Identifier x; l; u; e]) when Name.eq f (Name.of_string "forall") ->
      let sub = Substitution.singleton x u in 
      let bound = bound x l u in
      let e' = Substitution.apply AST.Infix.(bound =>@ e) sub in
        e'
    | _ as i -> i

  let extend_id (x : AST.id) (i : int) : AST.id = match x with
    | AST.Var n -> AST.Var (Name.set_counter n i)
    | AST.IndexedVar (n, e) ->
      let n' = Name.set_counter n i in
        AST.IndexedVar (n', e)

  let simplify_ante_interpolant (strength : int) : t -> t = function
    | AST.FunCall (f, [AST.Identifier x; l; u; e]) when Name.eq f (Name.of_string "forall") ->
      let range = CCList.range 1 strength in
      let fresh_variables = range
        |> CCList.map (extend_id x) in
      let disjoint = [fresh_variables ; fresh_variables]
        (* grab all distinct pairs *)
        |> CCList.cartesian_product
        |> CCList.filter_map (fun xs -> match xs with [fst ; snd] -> Some (fst, snd) | _ -> None)
        |> CCList.filter (fun (x, y) -> x != y)
        (* convert to an expression *)
        |> CCList.map (fun (x, y) ->
            let x' = AST.Identifier x in
            let y' = AST.Identifier y in
            AST.Infix.( !@ (x' =@ y') )
          ) in
      (* generate the weak induction forms *)
      let formulas = fresh_variables
        |> CCList.map (fun fv -> weak_induction_form fv x l u e) in
      (* and conjoin *)
        CCList.fold_left AST.Infix.(&@) (AST.Infix.bool true) (formulas @ disjoint)
    | _ as i -> i
end

(* for sequence interpolants, our conditions are all in the form of validity of implications *)
(* that is, we wish to compute validity of A => S *)
let impl_validity
  ?(axioms=Theory.Defaults.all)
  (env : Types.Environment.t)
  (ante : Constraint.conjunction) (succ : Constraint.conjunction) : bool =
    (* negate the succedent *)
    let negate s = {
      Constraint.expression = AST.Infix.(!@) s.Constraint.expression;
      encoding = S.Expr.not s.Constraint.encoding;
    } in
    (* construct the formula A & !S *)
    let formula = ante @ (CCList.map negate succ) in
    let _ = if (Global.show_checking ()) then 
      CCFormat.printf "@[<v>[INTERPOLATION] Checking@;%a@]@." Constraint.format_conjunction formula in
    let answer = Constraint.check_wrt_theory env axioms formula in
    let _ = if (Global.show_checking ()) then
      CCFormat.printf "[INTERPOLATION] Result is %a@." Constraint.Answer.format answer in
    match answer with
      (* valid iff A & !S unsat *)
      | Constraint.Answer.Unsat -> true
      | _ -> false

(* surprisingly, don't have false as a default constraint *)
let c_false = Constraint.of_expr Types.Environment.empty (AST.Literal (AST.Boolean false))

(* the only other condition relies on the free variables used *)
module Variable = struct
  type t = AST.id

  let rec variables_in_expr : AST.expr -> t list = function
    | AST.Literal _ -> []
    | AST.Identifier i -> begin match i with
        | AST.IndexedVar (_, e) -> i :: (variables_in_expr e)
        | _ -> [i]
      end
    | AST.FunCall (f, args) ->
      if Operation.is_quantifier f then match args with
        | [AST.Identifier i; e] -> CCList.remove ~eq:(=) ~key:i (variables_in_expr e)
        | _ -> []
      else CCList.flat_map variables_in_expr args

  let variables_in_label : Program.Label.t -> t list = function
    | Program.Label.Assign (i, e) -> i :: (variables_in_expr e)
    | Program.Label.Assume (b) -> variables_in_expr b
    | Program.Label.Draw (i, e) -> i :: (variables_in_expr e)
    | Program.Label.Concrete c ->
      (variables_in_expr c.Program.Label.expression) @ (variables_in_expr c.Program.Label.cost)

  let rec intersect_list : 'a list list -> 'a list = function
    | [] -> []
    | ls :: [] -> ls
    | ls :: rest ->
      CCList.inter ~eq:(=) ls (intersect_list rest)
end

(* we'll parameterize generation of sequence interpolants by a strategy *)
type interpolant = t
module Strategy = struct
  type t = S of (Types.Environment.t -> Variable.t list -> interpolant list)

  let apply = function
    S s -> s
end

let default = Strategy.S (fun env -> fun vars -> [])

let overly_specific = Strategy.S (fun env -> fun vars ->
  let answer = Parse.parse_expr 
    "(i <= n) & 
    (i >= 0) & 
    (best <= i) & 
    (best >= 0) &
    (beta >. rat(0)) &
    (w == (rat(i) *. (beta /. rat(n)))) &
    forall(j, 0, i, 
      (abs(a[j] -. q[j]) <. (rat(2) /. e) *. log(rat(n) /. beta)) & 
      (a[best] >=. a[j])
    )"
  in [answer]
  )