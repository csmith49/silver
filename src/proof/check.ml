module S = SMT.Default

open CCFormat
open AST.Infix

type path = Trace.path
type trace = Trace.t

let pre_to_constraint (trace : trace) : AST.annotation -> Constraint.t = fun annot ->
  let env = trace |> CCList.hd |> fun s -> s.Trace.variables |> Trace.Vars.extend 0 in
  let expr = annot &. ((var "w") =. (int 0)) &. ((var "h") =. (bool false)) in
    Constraint.of_expr env expr

let post_to_constraint (trace : trace) : AST.annotation -> AST.cost -> Constraint.t = fun annot -> fun c ->
  let i = CCList.length trace in  
  let env = trace 
    |> CCList.last_opt 
    |> CCOpt.get_exn 
    |> fun s -> s.Trace.variables 
    |> Trace.Vars.extend i 
    |> Types.Environment.update (Name.of_string "betainternal") (Types.Base Types.Rational) in
  (* TODO : convert this to the positive form *)
  let c' = Trace.SSA.update_expr c env in
  let annot' = Trace.SSA.update_expr annot env in
  let expr = ((var "betainternal") =. c') &. ((var "betainternal") >= (int 0)) &.
    (!. (((var_i ("w", i) <= (var "betainternal"))) &.
    ((!. (var_i ("h", i))) =>. annot'))) in
  expr
    |> Simplify.simplify
    |> Constraint.of_expr env

(*  *)
let check
  ?(verbose=false)
  (env : Types.Environment.t)
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (pre : AST.annotation)
  (path : path) 
  (post : AST.annotation) 
  (cost : AST.cost) : (Trace.encoding * Constraint.Answer.t) option = 
    let theory = Theory.Defaults.all in
    let trace = Trace.of_path env path in
    let pre = pre_to_constraint trace pre in
    let post = post_to_constraint trace post cost in
    let encodings = 
      Trace.encode env strategy axioms trace |> 
      CCList.map (fun enc -> pre :: (enc @ [post])) in
    let i = CCList.length encodings in
    (* printing *)
    let _ = if verbose then printf "@[<v>[CHECKING] %d possibilities...@;@]" i else () in
    (* the actual computation *)
    let results = encodings
      |> CCList.mapi (fun i -> fun c ->
        let _ = if verbose then printf "@[<v>[CHECKING/ENCODING %d]@; @[%a@]@;@]" (i + 1) Trace.format c else () in 
        let answer = (c, Constraint.check_wrt_theory ~verbose:verbose env theory c) in
        let _ = if verbose then printf "@[<v>[CHECKING/RESULT %d]@; @[%a@]@;@]" (i + 1) Constraint.Answer.format (snd answer) else () in
      answer) in
    (* filtering the results *)
    results |> CCList.filter (fun p -> Constraint.Answer.is_unsat (snd p)) |> CCList.head_opt