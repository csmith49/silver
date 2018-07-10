module S = SMT.Default

open CCFormat
open AST.Infix

type path = Trace.path
type trace = Trace.t

module Answer = struct
  type t =
    | Correct of Abstraction.proof list
    | Incorrect
    | Unknown

  let of_answers : (path * Constraint.Answer.t) list -> t = fun answers ->
    (* if there are any unsat answers, we can generate proofs *)
    let correct_paths = answers
      |> CCList.filter (fun (p, ans) -> Constraint.Answer.is_unsat ans)
      |> CCList.map fst in
    if not (CCList.is_empty correct_paths) then
      let proofs = correct_paths
        |> CCList.map Abstraction.of_path in
      Correct proofs
    (* if there are any unknown results (and no unsat), we answer unknown *)
    else if CCList.exists (CCPair.map_snd Constraint.Answer.is_unknown) answers then
      Unknown
    else
      Incorrect
end

let check ?(verbose=false)
  (theory : Theory.t)
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (env : Types.Environment.t)
  (pre : AST.annotation)
  (path : path)
  (post : AST.annotation)
  (cost : AST.cost) : Answer.t =
    (* compute all possible axiomatizations *)
    let axiomatizations = path
      |> Trace.axiomatize env strategy axioms in
    (* pair up each path with the path encoding *)
    let paths = axiomatizations
      |> CCList.map (fun ax -> (ax, Trace.path_formula env pre ax post cost)) in
    (* now check each *)
    let answers = paths
      |> CCList.map (CCPair.map2 (Constraint.check_wrt_theory env theory)) in
    (* compile the answers *)
    Answer.of_answers answers