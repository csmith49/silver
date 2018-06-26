(* we operate over proofs from automata/abstraction.ml *)
module State = Abstraction.State
module Label = Abstraction.Label

type path = (State.t, Label.t) Graph.Path.t

(* goal number one is to be able to convert subgraphs into disjunctive encodings *)
module Edge = struct
  type t = {
    index : int;
    variables : Types.Environment.t;
  }

  (* given a bunch of environemnts, we want to find out how much each variable has changed *)
  let rec maximal_environment : Types.Environment.t list -> Types.Environment.t = function
    | [] -> raise (Invalid_argument "Can't compute maximal environment from an empty list")
    | env :: [] -> env
    | env :: rest -> Types.Environment.max env (maximal_environment rest)

  (* disjunction might be ragged - we generate frame formulas to unify the right-hand side *)
  let frame_formula (edge : t) (current : Types.Environment.t) : Constraint.conjunction = 
    let maximal = edge.variables |> Trace.Vars.extend edge.index in maximal
      |> Types.Environment.variables
      |> CCList.filter_map (fun x ->
          let mc = Types.Environment.get_counter x maximal in
          let cc = Types.Environment.get_counter x current in
          if mc = cc then None else
            let mx = AST.Identifier (AST.Var (Name.set_counter x mc)) in
            let cx = AST.Identifier (AST.Var (Name.set_counter x cc)) in
              Some AST.Infix.(mx =. cx)
        )
      |> CCList.map (Constraint.of_expr maximal)

  let of_traces : Trace.t list -> t = fun traces ->
    let i = traces
      |> CCList.map CCList.length
      |> CCList.fold_left max 1 in
    let env = traces
      |> CCList.filter_map Trace.environment
      |> maximal_environment in
    {
      index = i;
      variables = env;
    }

  let of_environment : Types.Environment.t -> t = fun env -> {
    variables = env;
    index = 1;
  }
end

type t = {
  paths : Trace.t list;
  left : Edge.t;
  right : Edge.t;
}

let eq : t -> t -> bool = fun l -> fun r ->
  (CCList.sort Pervasives.compare l.paths) = (CCList.sort Pervasives.compare r.paths)

(* to check, we must convert paths to traces - but traces use Program.State! *)
let rec path_to_program_path : path -> Program.path = function
  | [] -> []
  | (src, lbl, dest) :: rest ->
    let src' = Abstraction.State.to_program_state src in
    let dest' = Abstraction.State.to_program_state dest in
      (src', lbl, dest') :: (path_to_program_path rest)

(* construction from automata from state to state *)
let of_graph (left : Edge.t) 
  (source : State.t list) (dest : State.t list) 
  (proof : Abstraction.proof) : t option =
    let paths = Graph.bfs_list ~v_eq:State.eq source dest proof.DFA.delta in
    let concrete_paths = CCList.filter_map DFA.concretize paths in
    (* check if we lost any paths along the way *)
    if (CCList.length paths) = (CCList.length concrete_paths)
      then
        let traces = concrete_paths 
          |> CCList.sort Pervasives.compare 
          |> CCList.map path_to_program_path 
          |> CCList.map (Trace.of_path left.Edge.variables) in
        let right = Edge.of_traces traces in
        Some {
          paths = traces;
          left = left;
          right = right;
        }
      else None

let axiomatize (strategy : Trace.Strategy.t) (axioms : Probability.axiom list) : t -> t list = fun dis ->
  dis.paths
    |> CCList.map (Trace.axiomatize strategy axioms)
    |> CCList.cartesian_product
    |> CCList.map (fun concrete -> { dis with paths = concrete })

let encode : t -> Constraint.t = fun dis -> 
  let encodings = dis.paths
    |> CCList.map (Trace.to_constraint ~index:dis.left.Edge.index) in
  let frames = dis.paths
    |> CCList.map (fun t -> Trace.environment t |> CCOpt.get_exn)
    |> CCList.map (Edge.frame_formula dis.right) in
  let constraints = CCList.map2 (@) encodings frames 
    |> CCList.map (fun c -> CCList.fold_left Constraint.Mk.and_ Constraint.Mk.true_ c)
  in CCList.fold_left Constraint.Mk.or_ Constraint.Mk.false_ constraints

(* this might not be right *)
let to_graph : t -> (Abstraction.State.t, Abstraction.Label.t DFA.Alphabet.t) Graph.t = fun dis ->
  let paths = dis.paths |> CCList.map Trace.to_path in
  let graphs = paths 
    |> CCList.map (fun path -> Abstraction.of_path path |> fun abs -> abs.DFA.delta) in
  CCList.fold_left Graph.merge (fun _ -> []) graphs

(* printing and whatnot *)
let format f : t -> unit = fun dis ->
  CCFormat.fprintf f "@[<v>%a@;@]@."
    (CCFormat.list ~sep:(CCFormat.return "@;") Trace.format) dis.paths