open Disjunction

module State = Abstraction.State
type proof = Abstraction.proof

(* step 1 is to determine possible states to merge two automata on *)
let merge_candidates (left : proof) (right : proof) : State.t list =
  (* just compute interesction of branch states *)
  let branch_states = left.DFA.states 
    |> CCList.filter (fun l -> CCList.mem State.eq l right.DFA.states)
    |> CCList.filter (fun s -> CCList.exists Program.Tag.is_branch s.State.tags) in
  branch_states

(* merge problems consist of a prefix, a left postfix, and a right postfix *)
type problem = {
  prefix : Disjunction.t;
  left : Disjunction.t;
  right : Disjunction.t;
}

(* we convert candidate states into problems *)
let candidate_to_problem
  (env : Types.Environment.t)
  (branch : State.t)
  (left : proof) (right : proof) : problem option =
    (* check to see the disjunction leading to the branch state is equivalent *)
    let edge = Disjunction.Edge.of_environment env in
    let prefix = Disjunction.of_graph edge [left.DFA.start] [branch] left in
    if not (CCOpt.equal Disjunction.eq 
      prefix 
      (Disjunction.of_graph edge [right.DFA.start] [branch] right)) 
    then None
    else try 
      let prefix = prefix |> CCOpt.get_exn in Some {
      prefix = prefix;
      left = Disjunction.of_graph prefix.Disjunction.right [branch] left.DFA.final left |> CCOpt.get_exn;
      right = Disjunction.of_graph prefix.Disjunction.right [branch] right.DFA.final right |> CCOpt.get_exn;
    } with _ -> None

(* we must check mergability wrt axioms *)
let axiomatize_problem
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (prob : problem) : problem list =
    (* axiomatize the individual disjunctions *)
    let prefixes = Disjunction.axiomatize strategy axioms prob.prefix in
    let lefts = Disjunction.axiomatize strategy axioms prob.left in
    let rights = Disjunction.axiomatize strategy axioms prob.right in
    (* and then pull them together *)
    [prefixes ; lefts ; rights]
      |> CCList.cartesian_product
      |> CCList.filter_map (fun xs -> match xs with
          | [p;l;r] -> Some {
            prefix = p;
            left = l;
            right = r;
          }
          | _ -> None)

(* and then see if a problem can actually be merged *)
let can_merge
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (env : Types.Environment.t)
  (pre : AST.annotation)
  (post : AST.annotation) (cost : AST.cost)
  (prob : problem) : bool =
    (* aliases *)
    let prefix = prob.prefix in
    let left = prob.left in
    let right = prob.right in
    (* encode pre and post conditions *)
    let pre = Check.pre_to_constraint Disjunction.(prefix.left.Edge.variables) pre in
    let post_left = Check.post_to_constraint
      Disjunction.(left.right.Edge.index)
      Disjunction.(left.right.Edge.variables)
      post cost in
    let post_right = Check.post_to_constraint
      Disjunction.(right.right.Edge.index)
      Disjunction.(right.right.Edge.variables)
      post cost in
    (* wrap everything together and encode disjunctions *)
    let left_constraint = Constraint.Mk.and_ (Disjunction.encode left) post_left in
    let right_constraint = Constraint.Mk.and_ (Disjunction.encode right) post_right in
    let conjunction =
      pre :: (Disjunction.encode prefix) :: (Constraint.Mk.or_ left_constraint right_constraint) :: [] in
    match Constraint.check_wrt_theory ~verbose:verbose env theory conjunction with
      | Constraint.Answer.Unsat -> true
      | _ -> false

(* can we convert a problem back to a proof *)
let problem_to_proof (left : proof) (right : proof) : problem -> proof = fun prob -> {
  DFA.states = CCList.sort_uniq Pervasives.compare (left.DFA.states @ right.DFA.states);
  start = left.DFA.start;
  final = CCList.sort_uniq Pervasives.compare (left.DFA.states @ right.DFA.states);
  delta = Graph.overlay 
    left.DFA.delta 
    (Graph.overlay 
      right.DFA.delta 
      (Graph.overlay 
        (Disjunction.to_graph prob.prefix)
        (Graph.overlay 
          (Disjunction.to_graph prob.left)
          (Disjunction.to_graph prob.right))));
}

(* step 4 is to try all possible merges *)
let merge
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (env : Types.Environment.t) 
  (pre : AST.annotation) 
  (post : AST.annotation) (cost : AST.cost) 
  (left : proof) (right : proof) : proof list =
    (* compute candidates *)
    let candidates = merge_candidates left right in
    (* generate base problems *)
    let problems = candidates
      |> CCList.filter_map (fun c -> candidate_to_problem env c left right) in
    (* axiomatize problems *)
    let problems = problems
      |> CCList.flat_map (axiomatize_problem strategy axioms) in
    (* filter problems to maintain only solutions *)
    let solutions = problems
      |> CCList.filter (can_merge ~verbose:verbose ~theory:theory env pre post cost) in
    (* convert solutions back to proofs *)
    solutions |> CCList.map (problem_to_proof left right)