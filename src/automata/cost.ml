type t = AST.expr

let format = AST.format

let max l r = AST.FunCall (Name.of_string "max", [l ; r])

let add = AST.Infix.(+.)

let zero : t = AST.Infix.int 0

let simplify = Simplify.simplify

let of_expr : AST.expr -> t = fun x -> x

let check_lt 
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (env : Types.Environment.t) (small : t) (large : t) : bool =
    let expr = AST.Infix.(small >= large) in
    let conjunct = [Constraint.of_expr env expr] in
    match Constraint.check_wrt_theory ~verbose:verbose env theory conjunct with
      | Constraint.Answer.Unsat -> true
      | _ -> false
