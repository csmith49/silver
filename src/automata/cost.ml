(* these are just expressions, but we alias them for type safety elsewhere *)
type t = AST.expr

let format = AST.format

(* we're doing a lot of addition, we can probably get rid of zeros and whatnot *)
let simplify = Simplify.simplify

(* aliases for simple arithmetic *)
let max l r = AST.FunCall (Name.of_string "max", [l ; r])
let add = AST.Infix.(+.@)
let zero : t = Parse.parse_expr "rat(0)"
let sum : t list -> t = fun xs -> simplify (CCList.fold_left add zero xs)

(* maybe we change the representation later? *)
let of_expr : AST.expr -> t = fun x -> x

(* to see if a cost is correct, we check validity of the following *)
(* pre & post => (cost <= beta) *)
let cost_acceptable ?(verbose=false) ?(theory=Theory.Defaults.all) (env : Types.Environment.t) 
  (pre : AST.annotation) (post : AST.annotation) (beta : AST.cost) (cost : t) : bool =
    let expr = AST.Infix.(
      (pre &@ post) &@ (cost >.@ beta)
    ) |> Simplify.simplify in
    let conjunct = [Constraint.of_expr env expr] in
    match Constraint.check_wrt_theory ~verbose:verbose env theory conjunct with
      | Constraint.Answer.Unsat -> true
      | _ -> false
