(* these are just expressions, but we alias them for type safety elsewhere *)
type t = AST.expr

let format = AST.format

let simplify = Simplify.simplify

let max l r = AST.FunCall (Name.of_string "max", [l ; r])
let add = AST.Infix.(+.)
let zero : t = AST.Infix.int 0
let sum : t list -> t = fun xs -> simplify (CCList.fold_left add zero xs)

(* maybe we change the representation later? *)
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
