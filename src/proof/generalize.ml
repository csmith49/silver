module State = Abstraction.State
type proof = Abstraction.proof

(* generalization problems have a prefix, a body, and a postfix *)
type problem = {
  prefix : Disjunction.t;
  body : Disjunction.t;
  postfix : Disjunction.t;
}

(* determine which states can act as a candidate *)
let generalize_candidates (proof : proof) : State.t list =
  (* proof better be loop-free... *)
  if DFA.loop_free ~s_eq:State.eq proof then
    (* find the states tagged with a loop *)
    let loop_states = proof.DFA.states
      |> CCList.filter (fun s -> CCList.exists Program.Tag.is_loop s.State.tags) in
    let paths = Graph.bfs_list ~v_eq:State.eq [proof.DFA.start] proof.DFA.final proof.DFA.delta in
    let states_along_paths = paths |> CCList.map Graph.Path.to_states in
    (* filter out states that don't show up exactly twice *)
    loop_states
      |> CCList.filter (fun s ->
        let check = (=) s in
        CCList.for_all (fun ss -> (CCList.count check ss) = 2) states_along_paths)
  else []

(* convert candidate states to problems *)
let candidate_to_problem
  (env : Types.Environment.t)
  (loop : State.t)
  (proof : proof) : problem option =
    let edge = Disjunction.Edge.of_environment env in
    (* prefix goes from start to first instance of loop *)
    let prefix = Disjunction.of_graph edge [proof.DFA.start] [loop] proof in
    match prefix with
      | Some prefix ->
        (* body goes from loop to loop *)
        let body = Disjunction.of_graph prefix.Disjunction.right [loop] [loop] proof in
        begin match body with
          | Some body ->
            (* and the postfix goes from loop to final - need to ensure every trace in disjunction visits loop only once *)
            let postfix = Disjunction.of_graph body.Disjunction.right [loop] proof.DFA.final proof in
            begin match postfix with
              | Some postfix ->
                let postfix = {
                  postfix with paths = postfix.Disjunction.paths
                    |> CCList.filter (fun trace -> trace
                      |> Trace.to_path
                      |> Graph.Path.to_states
                      |> fun s -> (CCList.count ((=) (Abstraction.State.to_program_state loop)) s) > 1
                    )
                } in Some {
                  prefix = prefix;
                  body = body;
                  postfix = postfix;
                }
              | None -> None end
          | None -> None end
      | None -> None

(* generalization should happen wrt axioms *)
let axiomatize_problem
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (prob : problem) : problem list =
    (* as elsewhere, we axiomatize the individual disjuncts *)
    let prefixes = Disjunction.axiomatize strategy axioms prob.prefix in
    let postfixes = Disjunction.axiomatize strategy axioms prob.postfix in
    let bodies = Disjunction.axiomatize strategy axioms prob.body in
    (* pull them together *)
    [prefixes ; bodies ; postfixes]
      |> CCList.cartesian_product
      |> CCList.filter_map (fun xs -> match xs with
          | [pre ; body ; post] -> Some {
              prefix = pre;
              body = body;
              postfix = post;
            }
          | _ -> None)

(* by merging everything together, we arrive back at a proof *)
let problem_to_proof (start : State.t) (final : State.t list) (prob : problem) : proof = {
  DFA.states = CCList.uniq ~eq:State.eq
    (Disjunction.states prob.prefix) @ (Disjunction.states prob.body) @ (Disjunction.states prob.postfix);
  start = start;
  final = final;
  delta = Graph.merge
    (Disjunction.to_graph prob.prefix)
    (Graph.merge
      (Disjunction.to_graph prob.body)
      (Disjunction.to_graph prob.postfix)
    );
}