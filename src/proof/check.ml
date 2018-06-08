module S = SMT.Default

open AST.Infix

type path = Trace.path
type trace = Trace.t

let pre_to_constraint (trace : trace) : AST.annotation -> Constraint.t = fun annot ->
  let env = trace |> CCList.hd |> fun s -> s.Trace.variables |> Trace.Vars.extend 0 in
  let expr = annot &. ((var "w") =. (int 0)) &. ((var "h") =. (bool false)) in
    Constraint.of_expr env expr

let post_to_constraint (trace : trace) : AST.annotation -> Constraint.t = fun annot ->
  let i = CCList.length trace in  
  let env = trace 
    |> CCList.last_opt 
    |> CCOpt.get_exn 
    |> fun s -> s.Trace.variables 
    |> Trace.Vars.extend i 
    |> Types.Environment.update (Name.of_string "beta") (Types.Base Types.Rational) in
  (* TODO : convert this to the positive form *)
  let expr = ((var "beta") >= (int 0)) &. 
    (!. (((var_i ("w", i) <= (var "beta"))) &.
    ((!. (var_i ("h", i))) =>. annot))) in
      Constraint.of_expr env expr

(*  *)
let vprint verbose s = if verbose then print_endline s else ()

let check
  ?(verbose=false)
  (env : Types.Environment.t)
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (pre : AST.annotation)
  (path : path) 
  (post : AST.annotation) : (Trace.encoding * Constraint.Answer.t) option = 
    let theory = Theory.Defaults.log in
    let trace = Trace.of_path env path in
    let pre = pre_to_constraint trace pre in
    let post = post_to_constraint trace post in
    let encodings = 
      Trace.encode env strategy axioms trace |> 
      CCList.map (fun enc -> pre :: (enc @ [post])) in
    let i = CCList.length encodings in
    (* printing *)
    let _ = vprint verbose 
      ("[CHECKING] " ^ (string_of_int i) ^ " possibilities...") in
    (* the actual computation *)
    let results = encodings
      |> CCList.mapi (fun i -> fun c ->
        let _ = vprint verbose 
          ("[CHECKING / ENCODING " ^ 
            (string_of_int (i + 1)) ^ "] " ^ 
            (Trace.encoding_to_string c)) in
        let answer = (c, Constraint.check_wrt_theory ~verbose:verbose env theory c) in
        let _ = vprint verbose
          ("[CHECKING / RESULT " ^ 
            (string_of_int (i + 1)) ^ "] " ^ 
            (Constraint.Answer.to_string (snd answer))) in
        answer) in
    (* filtering the results *)
    results |> CCList.filter (fun p -> Constraint.Answer.is_unsat (snd p)) |> CCList.head_opt