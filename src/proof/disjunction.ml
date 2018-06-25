(* we operate over proofs from automata/abstraction.ml *)
module State = Abstraction.State
module Label = Abstraction.Label

type path = (State.t, Label.t) Graph.Path.t

(* goal number one is to be able to convert subgraphs into disjunctive encodings *)
type disjunction = path list

(* we extend bfs from automata/graph.ml to return *all* loop-free paths *)
let bfs_list (source : 'v list) (dest : 'v list) (g : (State.t, Label.t DFA.Alphabet.t) Graph.t) : (State.t, Label.t DFA.Alphabet.t) Graph.Path.t list =
  (* aux function that operates over paths *)
  let rec aux = fun paths ->
    (* we need to check if paths have reached the destination *)
    let reaches_dest = fun path -> path
      |> Graph.Path.to_states |> CCList.last_opt
      |> CCOpt.exists (fun v -> CCList.mem State.eq v dest) in
    (* split the paths into those reaching the destination and those that need to be extended *)
    let finished, ongoing = CCList.partition reaches_dest paths in
    (* extend ongoing and filter out paths with loops *)
    let ongoing = ongoing
      |> CCList.flat_map (fun path -> Graph.extend path g)
      |> CCList.filter (fun path -> not (Graph.Path.has_loop ~v_eq:State.eq path)) in
    (* recurse if necessary *)
    if CCList.is_empty ongoing then finished else finished @ (aux ongoing) in
  (* generate initial paths out of source *)
  let init_paths = source |> CCList.flat_map (fun v -> Graph.step v g) |> CCList.map Graph.Path.of_step in
    aux init_paths

let of_graph (source : 'v list) (dest : 'v list) 
  (g : (State.t, Label.t DFA.Alphabet.t) Graph.t) : disjunction option  =
    let paths = bfs_list source dest g in
    let concrete_paths = CCList.filter_map DFA.concretize paths in
    if (CCList.length concrete_paths) = (CCList.length paths) 
      then Some (concrete_paths |> CCList.sort Pervasives.compare)
      else None

(* individual paths are encoded by conjunctive encodings *)
type conjunctive_enc = Trace.encoding

(* while collections of paths are disjunctive encodings *)
type disjuntive_enc = conjunctive_enc list

(* a disjunctive encoding requires an input index, and picks a set of semantics for every prob assignment *)
let rec path_to_program_path : path -> Trace.path = function
  | [] -> []
  | (src, lbl, dest) :: rest ->
    let src' = Abstraction.State.to_program_state src in
    let dest' = Abstraction.State.to_program_state dest in
      (src', lbl, dest') :: (path_to_program_path rest)

let path_to_trace (env : Types.Environment.t) : path -> Trace.t = fun p -> p
  |> path_to_program_path
  |> Trace.of_path env

let to_encoding (index : int) (env : Types.Environment.t)
  (strat : Trace.Strategy.t) (axioms : Probability.axiom list) : disjunction -> disjuntive_enc list = 
    fun dis -> dis
      |> CCList.map (path_to_trace env)
      |> CCList.map (Trace.encode ~index:index env strat axioms)
      |> CCList.cartesian_product
      
(* constraints are conjunctive, so we have to flatten if we want to actually check a disjunctive encoding *)
let encoding_to_constraint : disjuntive_enc -> Constraint.t = fun ds -> ds
  |> CCList.map (fun cj -> CCList.fold_left Constraint.Mk.and_ Constraint.Mk.true_ cj)
  |> CCList.fold_left Constraint.Mk.or_ Constraint.Mk.false_
  