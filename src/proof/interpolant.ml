(* we'll end up doing some direct manipulation of formulae *)
module S = SMT.Default

(* an interpolant is just a constraint - we maintain our ast and the logical encoding *)
type t = AST.expr

(* for sequence interpolants, our conditions are all in the form of validity of implications *)
(* that is, we wish to compute validity of A => S *)
let impl_validity (ante : Constraint.conjunction) (succ : Constraint.conjunction) : bool =
  (* negate the succedent *)
  let negate s = {
    Constraint.expression = AST.Infix.(!.) s.Constraint.expression;
    encoding = S.Expr.not s.Constraint.encoding;
  } in
  (* construct the formula A & !S *)
  let formula = ante @ (CCList.map negate succ) in
  let _ = if (Global.show_checking ()) then 
    CCFormat.printf "@[<v>[INTERPOLATION] Checking@;%a@]@." Constraint.format_conjunction formula in
  let answer = Constraint.check formula in
  let _ = if (Global.show_checking ()) then
    CCFormat.printf "[INTERPOLATION] Result is %a@." Constraint.Answer.format answer in
  match answer with
    (* valid iff A & !S unsat *)
    | Constraint.Answer.Unsat -> true
    | _ -> false

(* infix version, because I can't stop *)
let ( => ) (ante : Constraint.conjunction) (succ : Constraint.conjunction) : bool = 
  impl_validity ante succ

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
        | [AST.Identifier i; e] -> CCList.remove (=) i (variables_in_expr e)
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
    "forall(j, ((j > 0) & ( j <= i) & isint(j)) => abs(a[j] - q[j]) < (2 / e) * log(n / beta))" 
  in [answer]
  )