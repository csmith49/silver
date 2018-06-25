(* compute set of states a merge might occur on *)
let merge_candidates (left : Abstraction.proof) (right : Abstraction.proof) : Abstraction.State.t list =
  let candidate_states = left.DFA.states
    |> CCList.filter (fun l -> CCList.mem Abstraction.State.eq l right.DFA.states) in
  candidate_states
    |> CCList.filter (fun s ->
      let ld = Disjunction.of_graph [left.DFA.start] [s] left.DFA.delta in
      let rd = Disjunction.of_graph [right.DFA.start] [s] right.DFA.delta in
        (CCOpt.is_some ld) && (CCOpt.is_some rd) && (ld = rd)
    )

(* checking a candidate involves finding an interpolant, and we already assume everything is encoded *)
let check_candidate (pre : Constraint.t) (post_left : Constraint.t) (post_right : Constraint.t) (candidate : Abstraction.State.t) : Interpolant.interpolant option =
