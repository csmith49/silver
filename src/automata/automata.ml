(* classic automata representation - the transition relation is represented by a graph *)
type ('s, 'w) t = {
  states : 's list;
  start : 's;
  delta : ('s, 'w) Graph.t;
  final : 's list;
}

type ('s, 'w) path = ('s, 'w) Graph.Path.t

(* consume a single symbol non-deterministically *)
let consume_letter ?(l_eq = (=)) (start : 's) (letter : 'w) (automata : ('s, 'w) t) : 's list =
  let edges_out = automata.delta start in
  let f = fun (lbl, dest) -> if l_eq lbl letter then Some dest else None in
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
    let edges' = CCList.map (fun (lbl, dest) -> " --{" ^ (lp lbl) ^ "}-> " ^ (sp dest)) (automata.delta state) in
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