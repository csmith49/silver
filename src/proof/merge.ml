module State = Abstraction.State
type proof = Abstraction.proof

(* step 1 is to determine possible states to merge two automata on *)
let merge_candidates (left : proof) (right : proof) : State.t list =
  (* left and right must be loop-free *)
  if (Abstraction.loop_free left) && (Abstraction.loop_free right) then
  (* just compute interesction of branch states *)
  let branch_states = left.Abstraction.automata.DFA.states 
    |> CCList.filter (fun l -> CCList.mem State.eq l right.Abstraction.automata.DFA.states)
    |> CCList.filter (fun s -> CCList.exists Program.Tag.is_branch s.State.tags) in
  branch_states
  (* if l/r not loop-free, no possible states *)
  else []

(* merge problems consist of a prefix, a left postfix, and a right postfix *)
type problem = {
  prefix : Disjunction.t;
  left : Disjunction.t;
  right : Disjunction.t;
}

(* printing *)
let format f : problem -> unit = fun prob ->
  CCFormat.fprintf f "@[<v>Prefix:@;%a@;Left:@;%a@;Right:@;%a@;@]@."
    Disjunction.format prob.prefix
    Disjunction.format prob.left
    Disjunction.format prob.right

(* we convert candidate states into problems *)
let candidate_to_problem
  (env : Types.Environment.t)
  (branch : State.t)
  (left : proof) (right : proof) : problem option =
    (* check to see the disjunction leading to the branch state is equivalent *)
    let edge = Disjunction.Edge.of_environment env in
    let prefix = 
      Disjunction.of_graph edge [left.Abstraction.automata.DFA.start] [branch] left in
    if not (CCOpt.equal Disjunction.eq 
      prefix 
      (Disjunction.of_graph edge [right.Abstraction.automata.DFA.start] [branch] right)) 
    then None
    else try 
      let prefix = prefix |> CCOpt.get_exn in Some {
      prefix = prefix;
      left = Disjunction.of_graph 
        prefix.Disjunction.right 
        [branch] left.Abstraction.automata.DFA.final left 
          |> CCOpt.get_exn;
      right = Disjunction.of_graph 
        prefix.Disjunction.right
        [branch] right.Abstraction.automata.DFA.final right 
          |> CCOpt.get_exn;
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
    let _ = if verbose then
      CCFormat.printf "@[[MERGING] Checking problem@;%a@;@]@."
        format prob in
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
    match Constraint.check_wrt_theory env theory conjunction with
      | Constraint.Answer.Unsat -> true
      | _ -> false

(* can we convert a problem back to a proof *)
let to_proof 
  (start : State.t) (final : State.t list)
  (left_cost : AST.expr) (right_cost : AST.expr) : problem -> proof = fun prob ->
  let automata = {
    DFA.states = CCList.uniq State.eq (
        (Disjunction.states prob.prefix) @ 
        (Disjunction.states prob.left) @ 
        (Disjunction.states prob.right)
      );
    DFA.start = start;
    DFA.final = final;
    DFA.delta = Graph.merge
      (Disjunction.to_graph prob.prefix)
      (Graph.merge
        (Disjunction.to_graph prob.left)
        (Disjunction.to_graph prob.right)
      );
  } in
  let cost = Cost.(max left_cost right_cost) in
  {
    Abstraction.automata = automata;
    cost = cost;
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
    let _ = if verbose then 
      CCFormat.printf "[MERGING] %d candidate point(s).@." (CCList.length candidates) in
    (* generate base problems *)
    let problems = candidates
      |> CCList.filter_map (fun c -> candidate_to_problem env c left right) in
    (* axiomatize problems *)
    let problems = problems
      |> CCList.flat_map (axiomatize_problem strategy axioms) in
    let _ = if verbose then
      CCFormat.printf "[MERGING] %d axiomatizations at candidate point.@." (CCList.length problems) in
    (* filter problems to maintain only solutions *)
    let solutions = problems
      |> CCList.filter (can_merge ~verbose:verbose ~theory:theory env pre post cost) in
    let _ = if verbose then
      CCFormat.printf "[MERGING] %d resulting solution(s).@." (CCList.length solutions) in
    (* convert solutions back to proofs *)
    let start = left.Abstraction.automata.DFA.start in
    let final = left.Abstraction.automata.DFA.final in
    let left_cost = left.Abstraction.cost in
    let right_cost = right.Abstraction.cost in
    solutions |> CCList.map (to_proof start final left_cost right_cost)

let merge_abstraction
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (env : Types.Environment.t)
  (pre : AST.annotation) (post : AST.annotation) (cost : AST.cost)
  (abs : Abstraction.t) : (int * int * proof) list =
    let _ = if verbose then
      CCFormat.printf "[MERGE] Initiating merging...@." in
    (* we pick some defaults - these could be propagated using optional params *)
    let strategy = Trace.beta_strat in
    let axioms = Probability.Laplace.all @ Probability.Bernoulli.all in
    (* if there aren't enough things to merge, don't bother *)
    if (CCList.length abs) < 2 then 
      let _ = if verbose then CCFormat.printf "[MERGE] Abstraction too small.@." in [] else
    (* index the proofs and construct all pairs to be checked *)
    let indexed = CCList.mapi CCPair.make abs in
    let indices = indexed |> CCList.map fst in
    let pairs = [indices ; indices]
      |> CCList.cartesian_product
      |> CCList.filter_map (fun xs -> match xs with
          | [x ; y] -> Some (x, y)
          | _ -> None)
      |> CCList.filter (fun (x, y) -> x < y) in
    let merges = pairs
      |> CCList.flat_map (fun (l, r) ->
          let left = CCList.assoc ~eq:(=) l indexed in
          let right = CCList.assoc ~eq:(=) r indexed in
          let merges = merge ~verbose:verbose ~theory:theory
            strategy axioms env
            pre post cost
            left right in
          merges |> CCList.map (fun p -> (l, r, p))) in
    let _ = if verbose then
      CCFormat.printf "[MERGE] Found %d merges.@." (CCList.length merges) in
    merges