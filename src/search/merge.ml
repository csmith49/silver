module State = Abstraction.State
type proof = Abstraction.proof

(* merge problems consist of a prefix, a left postfix, and a right postfix *)
type problem = {
  prefix : Disjunction.t;
  left : Disjunction.t;
  right : Disjunction.t;
}

(* printing *)
let format f : problem -> unit = fun prob ->
  CCFormat.fprintf f "@[<v>Prefix +------->@;%a@;Left +--------->@;%a@;Right +-------->@;%a@]"
    Disjunction.format prob.prefix
    Disjunction.format prob.left
    Disjunction.format prob.right

(* step 1 is to determine possible states to merge two automata on *)
let candidates (left : proof) (right : proof) : State.t list =
  (* left and right must be loop-free *)
  if (Abstraction.loop_free left) && (Abstraction.loop_free right) then
    (* just compute intersection of branch states *)
    let left_branch_states = left.Abstraction.automata.DFA.states
      |> CCList.filter (fun s -> CCList.exists Program.Tag.is_branch s.State.tags) in
    let right_branch_states = right.Abstraction.automata.DFA.states
      |> CCList.filter (fun s -> CCList.exists Program.Tag.is_branch s.State.tags) in
    CCList.inter ~eq:State.eq left_branch_states right_branch_states
  (* if l/r not loop-free, no possible states *)
  else []

(* intersection over lists *)
let rec intersect ?(eq=(=)) : 'a list list -> 'a list = function
  | [] -> []
  | a :: [] -> a
  | a :: rest ->
    CCList.inter ~eq:eq a (intersect ~eq:eq rest)

(* building problems from states and the dfas *)
let to_problem
  (env : Types.Environment.t)
  (branch_point : State.t)
  (start : State.t) (final : State.t list)
  (left : proof) (right : proof) : problem option =
    let edge = Disjunction.Edge.of_environment env in
    (* check the disjunction leading to branch point is the same *)
    let prefix = Disjunction.of_graph edge [start] [branch_point] left in
    let prefix' = Disjunction.of_graph edge [start] [branch_point] right in
    if not ((CCOpt.equal Disjunction.eq) prefix prefix') then None else try
      (* this part can fail, as the prefix might not be constructable *)
      let prefix = prefix |> CCOpt.get_exn in
      let edge = prefix.Disjunction.right in
      (* construct left and right disjunctions *)
      let left = Disjunction.of_graph edge [branch_point] final left 
        |> CCOpt.get_exn in
      let right = Disjunction.of_graph edge [branch_point] final right 
        |> CCOpt.get_exn in
      (* check to make sure left goes through one branch, and right through the other *)
      let left_tag = left.Disjunction.paths
        |> CCList.map CCList.hd
        |> CCList.map (fun step -> step.Trace.step)
        |> CCList.map (fun (src, lbl, dest) -> dest)
        |> CCList.map (fun state -> state.Trace.State.tags |> CCList.filter Program.Tag.is_assumption)
        |> intersect
        |> CCList.hd in
      let right_tag = right.Disjunction.paths
        |> CCList.map CCList.hd
        |> CCList.map (fun step -> step.Trace.step)
        |> CCList.map (fun (src, lbl, dest) -> dest)
        |> CCList.map (fun state -> state.Trace.State.tags |> CCList.filter Program.Tag.is_assumption)
        |> intersect
        |> CCList.hd in
      if Program.Tag.complementary left_tag right_tag then
        Some {
          prefix = prefix;
          left = left;
          right = right;
        }
      else None
    with _ -> None

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
    let _ = if (Global.show_checking ()) then
      CCFormat.printf "@[[MERGING] Checking problem@;%a@;@]@."
        format prob in
    (* aliases *)
    let prefix = prob.prefix in
    let left = prob.left in
    let right = prob.right in
    let middle_left = AST.Literal (AST.Boolean false) in
    let middle_right = AST.Literal (AST.Boolean true) in
    let prefix_encoding = Disjunction.encode pre prefix middle_left in
    let left_encoding = Disjunction.encode_with_cost middle_right left post cost in
    let right_encoding = Disjunction.encode_with_cost middle_right right post cost in
    let encoding = Constraint.Mk.(and_ prefix_encoding (or_ left_encoding right_encoding)) in
    match Constraint.check_wrt_theory ~verbose:(Global.show_checking ()) env theory [encoding] with
      | Constraint.Answer.Unsat -> true
      | _ -> false

(* can we convert a problem back to a proof *)
(* TODO : this handles sequential ifs, but not nested *)
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
    DFA.delta = fun n ->
      ((Disjunction.to_graph prob.prefix) n) @
      ((Disjunction.to_graph prob.left) n) @
      ((Disjunction.to_graph prob.right) n);
  } in
  {
    Abstraction.automata = automata;
    cost = Cost.(max left_cost right_cost);
  }

(* step 4 is to try all possible merges *)
let merge
  ?(verbose=false)
  ?(theory=Theory.Defaults.all)
  (left_index : int) (right_index : int)
  (strategy : Trace.Strategy.t)
  (axioms : Probability.axiom list)
  (env : Types.Environment.t) 
  (pre : AST.annotation) 
  (post : AST.annotation) (cost : AST.cost) 
  (left : proof) (right : proof) : proof list =
    (* compute candidates *)
    let candidates = candidates left right in
    let _ = if verbose then 
      CCFormat.printf "[MERGING %d/%d] %d candidate point(s).@." 
        left_index right_index (CCList.length candidates) in
    (* generate base problems *)
    let start = left.Abstraction.automata.DFA.start in
    let final = left.Abstraction.automata.DFA.final @ right.Abstraction.automata.DFA.final in
    let problems = candidates
      |> CCList.filter_map (fun c -> to_problem env c start final left right) in
    (* axiomatize problems *)
    let problems = problems
      |> CCList.flat_map (axiomatize_problem strategy axioms) in
    let _ = if verbose then
      CCFormat.printf "[MERGING %d/%d] %d total axiomatizations.@." 
        left_index right_index (CCList.length problems) in
    (* filter problems to maintain only solutions *)
    let solutions = problems
      |> CCList.filter (can_merge ~verbose:verbose ~theory:theory env pre post cost) in
    let _ = if verbose then
      CCFormat.printf "[MERGING %d/%d] %d resulting solution(s).@." 
        left_index right_index (CCList.length solutions) in
    (* convert solutions back to proofs *)
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
            l r
            strategy axioms env
            pre post cost
            left right in
          merges |> CCList.map (fun p -> (l, r, p))) in
    let _ = if verbose then
      CCFormat.printf "[MERGE] Found %d merges.@." (CCList.length merges) in
    merges