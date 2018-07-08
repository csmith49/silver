module State = Abstraction.State
type proof = Abstraction.proof
type label = Program.Tag.t

type path = Disjunction.abs_path

(* gen. problems have a prefix, body, and postfix - we maintain label for ease of use *)
type problem = {
  label : label;
  prefix : Disjunction.t;
  body : Disjunction.t;
  postfix : Disjunction.t;
  fst : State.t list;
  snd : State.t list;
}

let format f = fun prob ->
CCFormat.fprintf f "@[<v>Prefix +------->@;%a@;Body +--------->@;%a@;Postfix +------>@;%a@]@;"
  Disjunction.format prob.prefix
  Disjunction.format prob.body
  Disjunction.format prob.postfix

let visits_twice (label : label) (path : path) : bool =
  let tags_along_path = path
    |> Graph.Path.to_states
    |> CCList.filter_map (fun s -> CCList.head_opt s.State.tags) in
  let count = CCList.count ((=) label) tags_along_path in
    count = 2

(* determine which tags are suitable candidates *)
let candidates (proof : proof) : label list =
  (* the proof really should be loop free *)
  if Abstraction.loop_free proof then
    (* find all possible loop tags *)
    let loop_tags = proof.Abstraction.automata.DFA.states
      |> CCList.flat_map (fun s -> s.State.tags)
      |> CCList.filter Program.Tag.is_loop in
    (* compute all the paths *)
    let start = proof.Abstraction.automata.DFA.start in
    let final = proof.Abstraction.automata.DFA.final in
    let paths = Graph.bfs_list ~v_eq:State.eq [start] final proof.Abstraction.automata.DFA.delta in
    (* now select loop tags that appear exactly twice in each trace *)
    loop_tags
      |> CCList.filter (fun t -> CCList.for_all (visits_twice t) paths)
  else []

(* find the pair of states with the provided label along the path *)
let loop_states (label : label) (path : path) : (State.t * State.t) option = path
  |> Graph.Path.to_states
  |> CCList.filter (fun s -> CCList.exists ((=) label) s.State.tags)
  |> fun xs -> match xs with
    | [fst ; snd] -> Some (fst, snd)
    | _ -> None

(* convert candidate tag to a problem *)
let to_problem
  (env : Types.Environment.t)
  (label : label)
  (start : State.t) (final : State.t list)
  (proof : proof) : problem option =
    let edge = Disjunction.Edge.of_environment env in
    (* compute the fst and snd loop points for all paths *)
    let start = proof.Abstraction.automata.DFA.start in
    let final = proof.Abstraction.automata.DFA.final in
    let fst, snd = proof.Abstraction.automata.DFA.delta
      |> Graph.bfs_list ~v_eq:State.eq [start] final
      |> CCList.filter_map (loop_states label)
      |> CCList.split in
    (* pull the prefix *)
    match Disjunction.of_graph edge [start] fst proof with
      | Some prefix ->
        let edge = prefix.Disjunction.right in
        begin match Disjunction.of_graph edge fst snd proof with
          | Some body ->
            let edge = body.Disjunction.right in
            begin match Disjunction.of_graph edge snd final proof with
              | Some postfix -> Some {
                  label = label;
                  prefix = prefix;
                  body = body;
                  postfix = postfix;
                  fst = fst;
                  snd = snd;
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
              prob with
              prefix = pre;
              body = body;
              postfix = post;
            }
          | _ -> None)

(* by merging everything together, we arrive back at a proof *)
let to_proof 
  (start : State.t) (final : State.t list) 
  (cost : Cost.t) (interpolant : Interpolant.t) (prob : problem) : proof =
    let fst = prob.fst
      |> CCList.map (fun s -> {s with State.annotation = Some interpolant}) in
    let snd = prob.snd
      |> CCList.map (fun s -> {s with State.annotation = Some interpolant}) in
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
        |> Graph.pinch ~v_eq:State.eq (fst @ snd)
    } in
    {
      cost = cost;
      automata = automata;
    }

let check_interpolant
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (interpolant : Interpolant.t)
  (pre : AST.annotation) (prob : problem) (post : AST.annotation) (cost : AST.cost) : bool =
    (* get a typing environment *)
    let env = Disjunction.Edge.environment prob.prefix.Disjunction.left in
    (* pre & prefix => interpolant *)
    let enc1 = Disjunction.encode pre prob.prefix interpolant in
    (* interp & body => interp *)
    let enc2 = Disjunction.encode interpolant prob.body interpolant in
    (* interp & postfix => post *)
    let enc3 = Disjunction.encode_with_cost interpolant prob.postfix post cost in
    (* now check, in sequence *)
    if Constraint.check_wrt_theory ~verbose:verbose env theory [enc1] |> Constraint.Answer.is_unsat then
      if Constraint.check_wrt_theory ~verbose:verbose env theory [enc2] |> Constraint.Answer.is_unsat then
        Constraint.check_wrt_theory ~verbose:verbose env theory [enc3] |> Constraint.Answer.is_unsat
      else false
    else false
    
(* check to see if a generalization is valid *)
let can_generalize
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  ?(strength=1)
  (strategy : Interpolant.Strategy.t)
  (env : Types.Environment.t)
  (pre : AST.annotation) (post : AST.annotation) (cost : AST.cost)
  (prob : problem) : Interpolant.t option =
    let _ = if (Global.show_checking ()) then
      CCFormat.printf "[GENERALIZING] Checking problem@;%a@." 
      format prob in
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
      CCList.find_opt (fun i -> 
        check_interpolant ~verbose:verbose ~theory:theory i pre prob post cost)
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
  ?(interpolant_strategy=Interpolant.default)
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
            interpolant_strategy
            env pre post cost proof in
          gens |> CCList.map (fun p -> (i, p))) in
    let _ = if verbose then
      CCFormat.printf "[GENERALIZE] Found %d generalizations.@." (CCList.length generalizations) in
    generalizations