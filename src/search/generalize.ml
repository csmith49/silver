module State = Abstraction.State
type proof = Abstraction.proof

(* generalization problems have a prefix, a body, and a postfix *)
type problem = {
  loop_points : State.t * State.t;
  prefix : Disjunction.t;
  body : Disjunction.t;
  postfix : Disjunction.t;
}

(* determine which states can act as a candidate *)
let candidates (proof : proof) : (State.t * State.t) list =
  (* proof better be loop-free... *)
  if Abstraction.loop_free proof then
    (* find the states tagged with a loop *)
    let loop_states = proof.Abstraction.automata.DFA.states
      |> CCList.filter (fun s -> CCList.exists Program.Tag.is_loop s.State.tags) in
    (* now compute all paths *)
    let start = proof.Abstraction.automata.DFA.start in
    let final = proof.Abstraction.automata.DFA.final in
    let paths = Graph.bfs_list ~v_eq:State.eq [start] final proof.Abstraction.automata.DFA.delta in
    (* consider all pairs of loop states *)
    let candidates = [loop_states ; loop_states]
      |> CCList.cartesian_product
      (* now filter out candidates that don't have the same loop tag *)
      |> CCList.filter (fun ls -> match ls with
          | [fst ; snd] ->
            let fst_tag = fst.State.tags |> CCList.filter Program.Tag.is_loop |> CCList.hd in
            let snd_tag = snd.State.tags |> CCList.filter Program.Tag.is_loop |> CCList.hd in
              fst_tag = snd_tag
          | _ -> false) in
    (* now we'll filter candidates by those realizable by all paths *)
    let loops_along_paths = paths 
      |> CCList.map Graph.Path.to_states
      |> CCList.map (CCList.filter (fun s -> CCList.exists Program.Tag.is_loop s.State.tags)) in
    candidates
      |> CCList.filter (fun ls -> CCList.for_all ((=) ls) loops_along_paths)
      |> CCList.filter_map (fun ls -> match ls with
          | [fst ; snd] -> Some (fst, snd)
          | _ -> None)
  else []

(* convert candidate states to problems *)
let to_problem
  (env : Types.Environment.t)
  (loop_points : State.t * State.t)
  (start : State.t) (final : State.t list)
  (proof : proof) : problem option =
    let edge = Disjunction.Edge.of_environment env in
    let fst, snd = loop_points in
    (* pull the prefix first *)
    match Disjunction.of_graph edge [start] [fst] proof with
      | Some prefix ->
        let edge = prefix.Disjunction.right in
        begin match Disjunction.of_graph edge [fst] [snd] proof with
          | Some body ->
            let edge = body.Disjunction.right in
            begin match Disjunction.of_graph edge [snd] final proof with
              | Some postfix -> Some {
                  loop_points = loop_points;
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
              loop_points = prob.loop_points;
              prefix = pre;
              body = body;
              postfix = post;
            }
          | _ -> None)

(* by merging everything together, we arrive back at a proof *)
let to_proof 
  (start : State.t) (final : State.t list) 
  (cost : Cost.t) (interpolant : Interpolant.t) (prob : problem) : proof = 
    let fst, snd = prob.loop_points in
    let fst' = { fst with annotation = Some interpolant } in
    let automata = {
      DFA.states = CCList.uniq ~eq:State.eq (
        (Disjunction.states prob.prefix) @ 
        (Disjunction.states prob.body) @ 
        (Disjunction.states prob.postfix));
      start = start;
      final = final;
      delta = Graph.merge
        (Disjunction.to_graph prob.prefix)
        (Graph.merge
          (Disjunction.to_graph prob.body)
          (Disjunction.to_graph prob.postfix)) 
        |> Graph.merge_states ~v_eq:State.eq fst snd
        |> Graph.map 
            (fun s -> if State.eq s fst then fst' else s)
            (fun s -> if State.eq s fst' then fst else s);
    } in
    {
      cost = cost;
      automata = automata;
    }

(* check to see if a generalization is valid *)
let can_generalize
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (strategy : Interpolant.Strategy.t)
  (env : Types.Environment.t)
  (pre : AST.annotation) (post : AST.annotation) (cost : AST.cost)
  (prob : problem) : Interpolant.t option =
    let _ = if verbose then
      CCFormat.printf "[GENERALIZING] Checking a problem@." in
    (* aliases *)
    let prefix = prob.prefix in
    let body = prob.body in
    let postfix = prob.postfix in
    (* pull the right variables out *)
    let pre_vars =
      (Disjunction.free_variables prefix) @ (Interpolant.Variable.variables_in_expr pre) in
    let body_vars = Disjunction.free_variables body in
    let post_vars =
      (Disjunction.free_variables postfix) @ (Interpolant.Variable.variables_in_expr post) in
    let variables = Interpolant.Variable.intersect_list [pre_vars ; body_vars ; post_vars] in
    (* pull interpolants *)
    let interpolants = Interpolant.Strategy.apply strategy env variables in
    (* get the edges more easily *)
    let pre_edge = prefix.Disjunction.left in
    let body_left = body.Disjunction.left in
    let body_right = body.Disjunction.right in
    let post_edge = postfix.Disjunction.right in
    (* encode the constraints *)
    let pre_constraint = Check.pre_to_constraint 
      pre_edge.Disjunction.Edge.variables
      pre in
    let post_constraint = Check.post_to_constraint
      post_edge.Disjunction.Edge.index
      post_edge.Disjunction.Edge.variables
      post cost in
    (* and the disjunctions *)
    let prefix_constraint = Disjunction.encode prefix in
    let body_constraint = Disjunction.encode body in
    let postfix_constraint = Disjunction.encode postfix in
    (* encoding interpolants using body left and body right *)
    let encode_interpolant i = (
        Constraint.of_expr body_left.Disjunction.Edge.variables (Disjunction.Edge.update_expr i body_left),
        Constraint.of_expr body_right.Disjunction.Edge.variables (Disjunction.Edge.update_expr i body_right)  
      ) in
    (* fidn the first interpolant where the appropriate conditions are met *)
    CCList.find_opt (fun i ->
        let left_i, right_i = encode_interpolant i in
          Interpolant.([pre_constraint ; prefix_constraint] => [left_i]) &&
          Interpolant.([left_i ; body_constraint] => [right_i]) &&
          Interpolant.([right_i ; postfix_constraint] => [post_constraint])) 
      interpolants
  
(* generalize a single proof *)
let generalize
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (index : int)
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (interpolant_strategy : Interpolant.Strategy.t)
  (env : Types.Environment.t)
  (pre : AST.annotation) (post : AST.annotation) (cost : AST.cost)
  (proof : proof) : proof list =
    (* compute candidates *)
    let candidates = candidates proof in
    let _ = if verbose then
      CCFormat.printf "[GENERALIZING %d] %d candidate point(s).@." index (CCList.length candidates) in
    (* generate base problems *)
    let start = proof.Abstraction.automata.DFA.start in
    let final = proof.Abstraction.automata.DFA.final in
    let problems = candidates
      |> CCList.filter_map (fun c -> to_problem env c start final proof) in
    (* axiomatize em *)
    let problems = problems
      |> CCList.flat_map (axiomatize_problem strategy axioms) in
    let _ = if verbose then
      CCFormat.printf "[GENERALIZING %d] %d axiomatizations.@." index (CCList.length problems) in
    (* filter problems to only get solutions *)
    let solutions = problems
      |> CCList.filter_map (fun prob ->
        match can_generalize ~verbose:verbose ~theory:theory interpolant_strategy env pre post cost prob with
          | Some interp -> Some (interp, prob)
          | _ -> None) in
    let _ = if verbose then
      CCFormat.printf "[GENERALIZING %d] %d resulting solution(s).@." index (CCList.length solutions) in
    (* convert solutions back to proofs *)
    solutions |> CCList.map (fun (i, p) -> to_proof start final cost i p)

(* attempt to generalize all abstractions *)
let generalize_abstraction 
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  ?(inteprolant_strategy=Interpolant.default)
  (env : Types.Environment.t)
  (pre : AST.annotation) (post : AST.annotation) (cost : AST.cost)
  (abs : Abstraction.t) : (int * proof) list =
    let _ = if verbose then CCFormat.printf "[GENERALIZE] Initiating generalize...@." in 
    (* pick some defaults - could be propagated using optional params *)
    let strategy = Trace.beta_strat in
    let axioms = Probability.Laplace.all @ Probability.Bernoulli.all in
    (* index the proofs *)
    let indexed = CCList.mapi CCPair.make abs in
    (* compute the generalizations *)
    let generalizations = indexed
      |> CCList.flat_map (fun (i, proof) ->
          let gens = generalize ~verbose:verbose ~theory:theory i
            strategy axioms
            inteprolant_strategy
            env pre post cost proof in
          gens |> CCList.map (fun p -> (i, p))) in
    let _ = if verbose then
      CCFormat.printf "[GENERALIZE] Found %d generalizations.@." (CCList.length generalizations) in
    generalizations