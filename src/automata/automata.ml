(* we have an infinite symbol set, so to complete our dfas we need more symbolic labels *)
module Symbol = struct
  (* we construct the powerset lattice over symbols *)
  type 'a t =
    | Singleton of 'a
    | Star
    | Complement of 'a list
  
  let to_string (p : 'a -> string) : 'a t -> string = function
    | Singleton x -> p x
    | Star -> "*"
    | Complement xs ->
      let xs' = CCList.map p xs |> CCString.concat ", " in
      "!{" ^ xs' ^ "}"

  (* assume left is a singleton - is it in the set described by right? *)
  let left_contains ?(s_eq = (=)) (left : 'a t) (right : 'a t) : bool = match left, right with
    | Singleton l, Star -> true
    | Singleton l, Singleton r -> s_eq l r
    | Singleton l, Complement rs -> not (CCList.mem s_eq l rs)
    | _ -> false

  (* making our life easier - functional construction mixes better with the rest of the infrastructure *)
  let lift : 'a -> 'a t = fun a -> Singleton a

  (* pulling a's out of t's might fail - we don't have a programmatic way to do it for stars and comps *)
  let concretize : 'a t -> 'a option = function
    | Singleton a -> Some a
    | _ -> None

  (* for concretizing later *)
  let is_positive : 'a t -> bool = function
    | Complement _ -> false
    | _ -> true

  let is_star : 'a t -> bool = function
    | Star -> true
    | _ -> false

  let get_basis : 'a t -> 'a list option = function
    | Complement xs -> Some xs
    | _ -> None
end

(* classic automata representation - the transition relation is represented by a graph *)
type ('s, 'w) t = {
  states : 's list;
  start : 's;
  delta : ('s, 'w Symbol.t) Graph.t;
  final : 's list;
}

type ('s, 'w) path = ('s, 'w Symbol.t) Graph.Path.t

type ('s, 'w) concrete_path = ('s, 'w) Graph.Path.t

(* concretizing a path may fail - there may be non-singletons *)
let concretize_step : ('s, 'w Symbol.t) Graph.Path.step -> ('s, 'w) Graph.Path.step option =
  fun (src, lbl, dest) -> match Symbol.concretize lbl with
    | Some lbl -> Some (src, lbl, dest)
    | _ -> None
let concretize_path : ('s, 'w) path -> ('s, 'w) concrete_path option = fun p ->
  let answer = CCList.filter_map concretize_step p in
  if (CCList.length answer) = (CCList.length p) then Some answer else None

(* consume a single symbol non-deterministically *)
let consume_letter ?(l_eq = (=)) (start : 's) (letter : 'w) (automata : ('s, 'w) t) : 's list =
  let edges_out = automata.delta start in
  let f = fun (lbl, dest) -> if (Symbol.left_contains ~s_eq:l_eq) (Symbol.lift letter) lbl
      then Some dest 
      else None in
    CCList.filter_map f edges_out

(* consume an entire word *)
let rec consume ?(l_eq = (=)) (start : 's) (word : 'w list) (automata : ('s, 'w) t) : 's list = match word with
  | [] -> [start]
  | l :: ls ->
    let next_states = consume_letter ~l_eq:l_eq l start automata in
    let step_again = fun state -> consume ~l_eq:l_eq state ls automata in
      CCList.flat_map step_again next_states

(* check to see if a word is accepted *)
let mem ?(s_eq = (=)) ?(l_eq = (=)) (word : 'w list) (automata : ('s, 'w) t) : bool =
  let terminal_states = consume ~l_eq:l_eq automata.start word automata in
  let accepting = fun state -> CCList.mem s_eq state automata.final in
    CCList.exists accepting terminal_states

(* to negate automata, we must first be able to complete it *)
(* to complete automata, we need to know where to add edges to the dump state *)
let positive_graph 
  ?(s_eq = (=)) (state : 's) (automata : ('s, 'w) t) (dump : 's) : ('s, 'w Symbol.t) Graph.t = 
    let symbols =state
      |> automata.delta
      |> CCList.map fst
      |> CCList.filter Symbol.is_positive in
    (* case 1 : there's a star *)
    if CCList.exists Symbol.is_star symbols then 
      fun _ -> [] else
    (* case 2 : there are no positive symbols *)
    if CCList.is_empty symbols then
      Graph.of_edge ~v_eq:s_eq (state, Symbol.Star, dump) else
    (* case 3 : no star, some positive symbols *)
    let comp = Symbol.Complement (CCList.filter_map Symbol.concretize symbols) in
      Graph.of_edge ~v_eq:s_eq (state, comp, dump)

let negative_graph
  ?(s_eq = (=)) (state : 's) (automata : ('s, 'w) t) (dump : 's) : ('s, 'w Symbol.t) Graph.t =
    let symbols = state
      |> automata.delta
      |> CCList.map fst
      |> CCList.filter_map Symbol.get_basis
      |> CCList.flatten in
    (* case 1 : there are no negative symbols *)
    if CCList.is_empty symbols then
      fun _ -> [] else
    (* case 2 : some symbols *)
    fun v -> if s_eq v state then (CCList.map (fun s -> (Symbol.lift s, dump)) symbols) else []

let complete_state ?(s_eq = (=)) 
  (state : 's) (automata : ('s, 'w) t) (dump : 's) : ('s, 'w Symbol.t) Graph.t =
    Graph.merge 
      (positive_graph ~s_eq:s_eq state automata dump)
      (negative_graph ~s_eq:s_eq state automata dump)

let complete ?(s_eq = (=)) ?(l_eq = (=)) (automata : ('s, 'w) t) (dump : 's) : ('s, 'w) t = 
  let add_dump = Graph.of_edge ~v_eq:s_eq (dump, Symbol.Star, dump) in
  let complete = automata.states
    |> CCList.map (fun s -> complete_state ~s_eq:s_eq s automata dump)
    |> CCList.fold_left Graph.merge add_dump in
  {
    states = dump :: automata.states;
    start = automata.start;
    final = automata.final;
    delta = Graph.merge complete automata.delta;
  }

(* negate an automata *)
let negate ?(s_eq = (=)) (automata : ('s, 'w) t) : ('s, 'w) t =
  let not_final = fun state -> not (CCList.mem s_eq state automata.final) in
  { automata with final = CCList.filter not_final automata.states; }

(* find a word in the language, if one exists *)
let find ?(s_eq = (=)) (automata : ('s, 'w) t) : ('s, 'w) path option =
  Graph.bfs ~v_eq:s_eq [automata.start] automata.final automata.delta

(* construct the intersection automata *)
let intersect ?(l_eq = (=)) (a : ('a, 'w) t) (b : ('b, 'w) t) : ('a * 'b, 'w) t = {
    states = a.states
      |> CCList.flat_map (fun a -> CCList.map (CCPair.make a) b.states);
    start = (a.start, b.start);
    delta = Graph.product ~e_eq:l_eq a.delta b.delta;
    final = a.final
      |> CCList.flat_map (fun a -> CCList.map (CCPair.make a) b.final);
  }

(* string conversion - really just used to provide a summary on the terminal *)
let to_string (sp : 's -> string) (lp : 'w -> string) (automata : ('s, 'w) t) : string =
  (* the local view just presents a state and all out-edges *)
  let local_view = fun state ->
    let state' = sp state in
    let edges' = CCList.map (fun (lbl, dest) -> " --{" ^ (Symbol.to_string lp lbl) ^ "}-> " ^ (sp dest)) (automata.delta state) in
      CCString.concat "\n\t" (state' :: edges') in
  (* so we just show the start state... *)
  let start' = "Start:\n\t" ^ (sp automata.start) in
  (* ...the final states... *)
  let final' = CCString.concat "\n\t" ("Final:" :: (CCList.map sp automata.final)) in
  (* ...and the edges, using local_view *)
  let edges' = CCList.map local_view automata.states in
  (* divider for A E S T H E T I C S *)
  let div = "+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+" in
  (* output *)
    CCString.concat "\n" (start' :: final' :: div :: edges' @ [div])

(* pruning just removes unreachable states *)
let prune ?(s_eq = (=)) : ('s, 'w) t -> ('s, 'w) t = fun automata -> 
  let reachable = Graph.reachable ~v_eq:s_eq [automata.start] automata.delta in {
    automata with 
      states = CCList.filter (fun state -> CCList.mem s_eq state reachable) automata.states;
      final = CCList.filter (fun state -> CCList.mem s_eq state reachable) automata.final;
  }