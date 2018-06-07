module S = SMT.Default

open AST.Infix

type path = Trace.path
type trace = Trace.t

let pre_to_constraint (trace : trace) : AST.annotation -> Constraint.t = fun annot ->
  let env = trace |> CCList.hd |> fun s -> s.Trace.variables in
  let expr = annot &. ((var "w") =. (int 0)) &. ((var "h") =. (bool false)) in
    Constraint.of_expr env expr

let post_to_constraint (trace : trace) : AST.annotation -> Constraint.t = fun annot ->
  let env = trace |> CCList.last_opt |> CCOpt.get_exn |> fun s -> s.Trace.variables in
  let i = CCList.length trace in
  let expr = !. (
      (
        (var_i ("w", i) <= (var "beta"))
      ) &.
      (
        (!. 
          (var_i ("h", i))
        ) =>. annot
      )
    ) in
    Constraint.of_expr env expr

(*  *)
let check
  (env : Types.Environment.t)
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (pre : AST.annotation)
  (path : path) 
  (post : AST.annotation) : Trace.encoding option = 
    let trace = Trace.of_path env path in
    let pre = pre_to_constraint trace pre in
    let post = post_to_constraint trace post in
    let encodings = Trace.encode env strategy axioms trace in
    let theory = Theory.Defaults.log in
    encodings 
      |> CCList.map (fun enc -> pre :: (enc @ [post]))
      |> CCList.filter (fun c -> Constraint.check_wrt_theory env theory c |> Constraint.Answer.is_unsat)
      |> CCList.head_opt