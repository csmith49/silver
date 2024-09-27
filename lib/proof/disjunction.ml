open Core
open Automata
open Logic

(* we operate over proofs from automata/abstraction.ml *)
module State = Abstraction.State
module Label = Abstraction.Label

type path = (State.t, Label.t) Graph.Path.t
type abs_path = (State.t, Label.t DFA.Alphabet.t) Graph.Path.t

(* goal number one is to be able to convert subgraphs into disjunctive encodings *)
module Edge = struct
  type t = {
    index : int;
    variables : Types.Environment.t;
  }

  let environment : t -> Types.Environment.t = fun edge ->
    Trace.Vars.extend edge.index edge.variables

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
              Some AST.Infix.(mx =@ cx)
        )
      |> CCList.map (Constraint.of_expr maximal)

  let of_traces ?(offset=0) : Trace.t list -> t = fun traces ->
    let i = traces
      |> CCList.map CCList.length
      |> CCList.map ((+) offset)
      |> CCList.fold_left max 1 in
    let env = traces
      |> CCList.filter_map Trace.environment
      |> maximal_environment in
    {
      index = i - 1;
      variables = Trace.Vars.extend (i - 1) env;
    }

  let of_environment : Types.Environment.t -> t = fun env -> 
    {
      variables = Trace.Vars.extend 1 env;
      index = 1;
    }

  let update_expr : AST.expr -> t -> AST.expr = fun e -> fun edge ->
    Trace.SSA.update_expr e edge.variables
end

type t = {
  paths : Trace.t list;
  left : Edge.t;
  right : Edge.t;
}

(* pull the states from every trace in the disjunction *)
let states : t -> State.t list = fun dis -> dis.paths
  |> CCList.map Trace.to_path
  |> CCList.flat_map Graph.Path.to_states
  |> CCList.map Abstraction.State.of_program_state

let eq : t -> t -> bool = fun l -> fun r ->
  (CCList.sort Stdlib.compare l.paths) = (CCList.sort Stdlib.compare r.paths)

(* to check, we must convert paths to traces - but traces use Program.State! *)
let rec path_to_program_path : path -> Program.path = function
  | [] -> []
  | (src, lbl, dest) :: rest ->
    let src' = Abstraction.State.to_program_state src in
    let dest' = Abstraction.State.to_program_state dest in
      (src', lbl, dest') :: (path_to_program_path rest)

let of_list (edge : Edge.t) (paths : abs_path list) : t option =
  let concrete_paths = CCList.filter_map DFA.concretize paths in
  (* check to see if we lost any *)
  if (CCList.length paths) = (CCList.length concrete_paths) then
    let traces = concrete_paths
      |> CCList.sort Stdlib.compare
      |> CCList.map path_to_program_path
      |> CCList.map (Trace.of_path edge.Edge.variables) in
    let right = Edge.of_traces ~offset:(edge.Edge.index) traces in Some {
      paths = traces;
      left = edge;
      right = right;
    }
  else None

(* construction from automata from state to state *)
let of_graph (left : Edge.t) 
  (source : State.t list) (dest : State.t list) 
  (proof : Abstraction.proof) : t option =
    let paths = Graph.bfs_list ~v_eq:State.eq 
      source dest proof.Abstraction.automata.DFA.delta in
    of_list left paths

(* try all simultaneous axiomatizations *)
let axiomatize (strategy : Trace.Strategy.t) (axioms : Probability.axiom list) : t -> t list = fun dis ->
  dis.paths
    |> CCList.map (Trace.axiomatize strategy axioms)
    |> CCList.cartesian_product
    |> CCList.map (fun concrete -> { dis with paths = concrete })

(* utility to collapse pre, dis, post into a single constraint *)
let collapse (pre : Constraint.t) (dis : Trace.encoding list) (post : Constraint.t) : Constraint.t =
  let encodings = dis
    |> CCList.map (CCList.fold_left Constraint.Mk.and_ Constraint.Mk.true_) in
  let disjunction = CCList.fold_left Constraint.Mk.or_ Constraint.Mk.false_ encodings in
    Constraint.Mk.(and_ (and_ pre disjunction) post)

(* attempt a simple encoding, otherwise go as complicated as necessary *)
let encode (pre : AST.annotation) (dis : t) (post : AST.annotation) : Constraint.t =
  let index = dis.left.Edge.index in
  let left_env = Edge.environment dis.left in
  let right_env = Edge.environment dis.right in
  let frames = dis.paths
    |> CCList.map (fun t -> Trace.environment t |> CCOption.get_exn_or "")
    |> CCList.map (Edge.frame_formula dis.right) in
  (* check if _all_ paths in dis can be made simple *)
  if CCList.for_all (Trace.can_simplify ~index:index left_env pre) dis.paths then
    (* if so, then we get by with a simple encoding *)
    let pre = Trace.Encode.simple_pre left_env pre in
    let post = Trace.Encode.just_simple_post right_env post in
    let encodings = dis.paths
      |> CCList.map (Trace.to_simple_constraint ~index:index) in
    let disjunction = CCList.map2 (@) encodings frames in
      collapse pre disjunction post
  else
    (* go complicated *)
    let pre = Trace.Encode.pre left_env pre in
    let post = Trace.Encode.just_post right_env post in
    let encodings = dis.paths
      |> CCList.map (Trace.to_constraint ~index:index) in
    let disjunction = CCList.map2 (@) encodings frames in
      collapse pre disjunction post

let encode_with_cost
  (pre : AST.annotation) (dis : t) (post : AST.annotation) (cost : AST.cost) : Constraint.t =
    let index = dis.left.Edge.index in
    let right_index = dis.right.Edge.index in
    let left_env = Edge.environment dis.left in
    let right_env = Edge.environment dis.right in
    let frames = dis.paths
      |> CCList.map (fun t -> Trace.environment t |> CCOption.get_exn_or "")
      |> CCList.map (Edge.frame_formula dis.right) in
    (* check if _all_ paths in dis can be made simple *)
    if CCList.for_all (Trace.can_simplify ~index:index left_env pre) dis.paths then
      (* if so, then we get by with a simple encoding *)
      let pre = Trace.Encode.simple_pre left_env pre in
      let post = Trace.Encode.simple_post right_index right_env post cost in
      let encodings = dis.paths
        |> CCList.map (Trace.to_simple_constraint ~index:index) in
      let disjunction = CCList.map2 (@) encodings frames in
        collapse pre disjunction post
    else
      (* go complicated *)
      let pre = Trace.Encode.pre left_env pre in
      let post = Trace.Encode.post right_index right_env post cost in
      let encodings = dis.paths
        |> CCList.map (Trace.to_constraint ~index:index) in
      let disjunction = CCList.map2 (@) encodings frames in
        collapse pre disjunction post

(* convert disjunction to abstraction graph *)
let to_graph : t -> (Abstraction.State.t, Abstraction.Label.t DFA.Alphabet.t) Graph.t = fun dis ->
  let paths = dis.paths |> CCList.map Trace.to_path in
  let graphs = paths
    |> CCList.map (Graph.of_path ~v_eq:Program.State.eq)
    |> CCList.map (Graph.map_edge DFA.Alphabet.lift)
    |> CCList.map (Graph.map Abstraction.State.of_program_state Abstraction.State.to_program_state) in
  CCList.fold_left Graph.merge (fun _ -> []) graphs

(* printing and whatnot *)
let format f : t -> unit = fun dis ->
  CCFormat.fprintf f "@[<v>%a@]"
    (CCFormat.list ~sep:(CCFormat.return "@;---@;") Trace.format) dis.paths

(* get the free variables in the union of all traces *)
let free_variables : t -> Interpolant.Variable.t list = fun dis -> dis.paths
  |> CCList.flat_map Trace.to_word
  |> CCList.flat_map Interpolant.Variable.variables_in_label