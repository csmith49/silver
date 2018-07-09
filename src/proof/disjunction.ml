(* we operate over proofs from automata/abstraction.ml *)
module State = Abstraction.State
module Label = Abstraction.Label

module Index = Trace.Index

type path = (State.t, Label.t) Graph.Path.t
type abstract_path = (State.t, Label.t DFA.Alphabet.t) Graph.Path.t

type t = Trace.path list

(* frame provides an extension in utility to index, and helps us build frame constraints *)
module Frame = struct
  type t = Index.t

  let of_indices : Index.t list -> t = fun indices ->
    CCList.fold_left Index.merge Index.initial indices

  let frame_constraint (env : Types.Environment.t) (frame : t) (index : Index.t) : Constraint.t list =
    let env = Trace.Variables.extend env in
    let variables = Types.Environment.variables env in variables
      |> CCList.filter_map (fun x ->
        let fc = Index.get x frame in
        let ic = Index.get x index in
        if fc = ic then None else
          let fx = AST.Identifier (AST.Var (Name.set_counter x fc)) in
          let ix = AST.Identifier (AST.Var (Name.set_counter x ic)) in
            Some AST.Infix.(fx =@ ix)) 

  let square_up (env : Types.Environment.t) : (Constraint.t * Index.t) list -> (Constraint.t list) * Index.t = fun encodings ->
    let phis, indices = CCList.split encodings in
    let frame = of_indices indices in
    let constraints = encodings
      |> CCList.map (fun (phi, index) -> 
          let frames = frame_constraint env frame index in
            Constraint.conjunction (phi :: frames)) in
    (constraints, frame)     
end

(* we'll convert paths to traces, which use Program.State, not Abstraction.State *)
let rec path_to_trace_path : path -> Trace.path = function
  | [] -> []
  | (src, lbl, dest) :: rest ->
    let src' = Abstraction.State.to_program_state src in
    let dest' = Abstraction.State.to_program_state dest in
      (src', lbl, dest') :: (path_to_trace_path rest)

(* given abstract paths, try to concretize and convert to trace paths *)
let of_abstract_path_list : abstract_path list -> t option = fun paths ->
  let concrete_paths = CCList.filter_map DFA.concretize paths in
  (* check to see if we lost any *)
  if (CCList.length paths) = (CCList.length concrete_paths) then
    let trace_paths = concrete_paths
      |> CCList.sort_uniq ~cmp:Pervasives.compare
      |> CCList.map path_to_trace_path in
    Some trace_paths
  else None

(* construction from automata state to state *)
let of_graph (source : State.t list) (dest : State.t list) (proof : Abstraction.proof) : t option =
  let abstract_paths = Graph.bfs_list ~v_eq:State.eq 
    source dest proof.Abstraction.automata.DFA.delta in
  of_abstract_path_list abstract_paths

(* axiomatize all paths simultaneously *)
let axiomatize (env : Types.Environment.t) 
  (strategy : Trace.Strategy.t) (axioms : Probability.axiom list) : t -> t list = fun dis -> dis
    |> CCList.map (Trace.axiomatize env strategy axioms)
    |> CCList.cartesian_product

(* can simplify if _all_ paths can simplify *)
let is_simplifiable (env : Types.Environment.t) (pre : AST.annotation) : t -> bool = fun dis ->
  CCList.for_all (Trace.is_simplifiable env pre) dis

(* encoding is done mostly straightforward - note we always need to accept/return indices *)
let formula (env : Types.Environment.t) (index : Index.t)
  (pre : AST.annotation) (dis : t) (post : AST.annotation) (cost : AST.cost) : Constraint.t * Index.t =
    (* check to see if we can use simplified encoding *)
    if is_simplifiable env pre dis then
      let pre, index = Trace.to_constraint index (Trace.Annotation.simple_pre pre) in
      let phis, index = dis
        |> CCList.map (fun p -> Trace.to_constraint index (Trace.encode_simple p))
        |> Frame.square_up env in
      let post, index = Trace.to_constraint index (Trace.Annotation.simple_post cost post) in
        (Constraint.conjunction [pre ; Constraint.disjunction phis ; post], index)
    else
      let pre, index = Trace.to_constraint index (Trace.Annotation.pre pre) in
      let phis, index = dis
        |> CCList.map (fun p -> Trace.to_constraint index (Trace.encode p))
        |> Frame.square_up env in
      let post, index = Trace.to_constraint index (Trace.Annotation.post cost post) in
        (Constraint.conjunction [pre ; Constraint.disjunction phis ; post], index)

(* we have a few variants - just a precondition *)
let pre_formula (env : Types.Environment.t) (index : Index.t)
  (pre : AST.annotation) (dis : t) : Constraint.t * Index.t =
    (* check to see if we can use simplified encoding *)
    if is_simplifiable env pre dis then
      let pre, index = Trace.to_constraint index (Trace.Annotation.simple_pre pre) in
      let phis, index = dis
        |> CCList.map (fun p -> Trace.to_constraint index (Trace.encode_simple p))
        |> Frame.square_up env in
      (Constraint.conjunction [pre ; Constraint.disjunction phis], index)
    else
      let pre, index = Trace.to_constraint index (Trace.Annotation.pre pre) in
      let phis, index = dis
        |> CCList.map (fun p -> Trace.to_constraint index (Trace.encode p))
        |> Frame.square_up env in
      (Constraint.conjunction [pre ; Constraint.disjunction phis], index)
(* and just a postcondition *)
let post_formula (env : Types.Environment.t) (index : Index.t)
  (dis : t) (post : AST.annotation) (cost : AST.cost) : Constraint.t * Index.t =
    (* check to see if we can use simplified encoding *)
    if is_simplifiable env (AST.Literal (AST.Boolean true)) dis then
      let phis, index = dis
        |> CCList.map (fun p -> Trace.to_constraint index (Trace.encode_simple p))
        |> Frame.square_up env in
      let post, index = Trace.to_constraint index (Trace.Annotation.simple_post cost post) in
        (Constraint.conjunction [Constraint.disjunction phis ; post], index)
    else
      let phis, index = dis
        |> CCList.map (fun p -> Trace.to_constraint index (Trace.encode p))
        |> Frame.square_up env in
      let post, index = Trace.to_constraint index (Trace.Annotation.post cost post) in
        (Constraint.conjunction [Constraint.disjunction phis ; post], index)

(* convert disjunction to abstraction graph *)
let to_graph : t -> (Abstraction.State.t, Abstraction.Label.t DFA.Alphabet.t) Graph.t = fun dis ->
  let paths = dis in
  let graphs = paths
    |> CCList.map (Graph.of_path ~v_eq:Program.State.eq)
    |> CCList.map (Graph.map_edge DFA.Alphabet.lift)
    |> CCList.map (Graph.map Abstraction.State.of_program_state Abstraction.State.to_program_state) in
  CCList.fold_left Graph.merge (fun _ -> []) graphs

(* get the free variables in the union of all traces *)
let free_variables : t -> Interpolant.Variable.t list = fun dis -> dis
  |> CCList.flat_map Graph.Path.to_word
  |> CCList.flat_map Interpolant.Variable.variables_in_label