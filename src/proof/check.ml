module S = SMT.Default

open CCFormat
open AST.Infix

type path = Trace.path
type trace = Trace.t

let check_trace
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (env : Types.Environment.t)
  (pre : AST.annotation) 
  (trace : trace) 
  (post : AST.annotation) (cost : AST.cost) : Constraint.Answer.t =
    let encoding = Trace.encode env pre post cost trace in
      Constraint.check_wrt_theory ~verbose:verbose env theory encoding


module Answer = struct
  (* an answer here is either a set of proofs, incorrect, or unknown *)
  type t =
    | Correct of Abstraction.proof list
    | Incorrect
    | Unknown

  let of_answers : (Trace.t * Constraint.Answer.t) list -> t = fun answers ->
    (* if there are any unsat answers, it's correct *)
    let proofs = answers
      |> CCList.filter (fun (tr, answer) -> Constraint.Answer.is_unsat answer)
      |> CCList.map fst
      |> CCList.map Trace.to_path
      |> CCList.map Abstraction.of_path in
    if not (CCList.is_empty proofs) then (Correct proofs) 
    (* if there are any unknown results, then our answer is unknown *)
    else if CCList.exists (CCPair.map_snd Constraint.Answer.is_unknown) answers 
      then Unknown
      else Incorrect
end

(*  *)
let check
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (env : Types.Environment.t)
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (pre : AST.annotation)
  (path : path)
  (post : AST.annotation)
  (cost : AST.cost) : Answer.t =
    let trace = Trace.of_path env path in
    let axiomatizations = Trace.axiomatize strategy axioms trace in
    let i = CCList.length axiomatizations in
    let _ = if verbose then printf "@[<v>[CHECKING] %d possibilities...@;@]" i else () in
    let results = axiomatizations
      |> CCList.mapi (fun i -> fun c ->
          let _ = if verbose then
            printf "@[<v>[CHECKING/ENCODING %d]@; @[%a@]@;@]"
              (i + 1)
              Trace.format c
            else () in
          let answer = (c, check_trace ~verbose:(Global.show_checking ()) ~theory:theory env pre c post cost) in
          let _ = if verbose then 
            printf "@[<v>[CHECKING/RESULT %d]@; @[%a@]@;@]" 
              (i + 1) 
              Constraint.Answer.format (snd answer)
            else () in
          answer) in
    results |> Answer.of_answers