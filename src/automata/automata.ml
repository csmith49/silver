(* helper module for implementing the transition relation delta *)
module Graph = struct
  (* # the base types *)
  (* this is the "child" function - anything that can compute it can be a graph *)
  type ('v, 'e) t = 'v -> ('e * 'v) list

  (* paths hold a list of edges *)
  (* should probably hold them in reverse order, but y'know *)
  type ('v, 'e) path = ('v * 'e * 'v) list

  (* will be nice to tag vertices when appropriate *)
  type 'v tag = 'v -> bool

  (* # graph construction *)
  (* the empty graph contains no out-going edges *)
  let empty : ('v, 'e) t = fun _ -> []

  (* to see how graphs should/could be used, here's a simple func *)
  let rec reachable_states (ss : 'v list) (g : ('v, 'e) t) : 'v list =
    let out_edges = CCList.flat_map g ss in
    let one_away = CCList.map snd out_edges in
    if CCList.for_all (fun v -> List.mem v ss) one_away then ss else
      reachable_states (CCList.sort_uniq Pervasives.compare (ss @ one_away)) g

  (* builds a new function to worry about the edge *)
  (* definitely not the most efficient way to build the entire graph *)
  let add_edge (g : ('v, 'e) t) (e : ('v * 'e * 'v)) : ('v, 'e) t =
    let src, lbl, dest = e in
    fun v -> if v == src then (lbl, dest) :: (g v) else g v

  (* # utility functions for paths *)
  (* peel off the last state in a path *)
  let last_state : ('v, 'e) path -> 'v option = fun p ->
    CCOpt.map (fun (s, l, d) -> d) (CCList.last_opt p)

  (* given a path and a graph, find all one-edge extensions of the path in the graph *)
  let extend_path (g : ('v, 'e) t) (p : ('v, 'e) path) : ('v, 'e) path list =
    match last_state p with
      | None -> []
      | Some v ->
        let out_edges = CCList.map (fun (l, d) -> (v, l, d)) (g v) in
          CCList.map (fun e -> p @ [e]) out_edges

  (* printing paths *)
  let rec path_to_string (np : 'v -> string) (ep : 'e -> string) (p : ('v, 'e) path) : string = match p with
    | [] -> "<empty path>"
    | (s, l, d) :: [] ->
      let s' = np s in
      let d' = np d in
      let l' = ep l in
        s' ^ " -{" ^ l' ^ "}-> " ^ d'
    | (s, l, _) :: xs ->
      let s' = np s in
      let l' = ep l in
        s' ^ " -{" ^ l' ^ "}-> " ^ (path_to_string np ep xs) 

  (* # finding paths and whatnot *)
  (* from a graph and two sets of v's, find a path connecting them (if one exists) *)
  let get_path (g : ('v, 'e) t) (init : 'v list) (acc : 'v list) : ('v, 'e) path option =
    (* all the work is done by an auxilliary function *)
    let rec aux (current : ('v, 'e) path list) (seen : 'v tag) (g : ('v, 'e) t) =
      let already_seen = fun p ->
        CCOpt.get_or ~default:true (CCOpt.map seen (last_state p)) in
      (* which finds all one-edge extensions reaching new states *)
      let extended = current
        |> CCList.flat_map (extend_path g)
        |> CCList.filter (fun p -> not (already_seen p)) in
      let reached_states = CCList.keep_some (CCList.map last_state extended) in
      (* before checking to see if any reach a final state *)
      let accepting_paths = extended
        |> CCList.filter (fun p -> CCOpt.exists (fun v -> List.mem v acc) (last_state p)) in
      (* and then recursing *)
      match accepting_paths with
        | x :: _ -> Some x
        | [] -> 
          let seen' = fun v -> (seen v) || (List.mem v reached_states) in
            aux extended seen' g
    in
    (* initialization *)
    let initial_edges = init
      |> CCList.flat_map (fun v -> CCList.map (fun (l, d) -> CCList.pure (v, l, d)) (g v)) in
    aux initial_edges (fun _ -> false) g
end

(* the type --- list of states, start state, delta, accepting states *)
type ('s, 'e) t = A of 's list * 's * ('s, 'e) Graph.t * 's list

(* accessor functions, to make life slightly easier *)
(* should probably just implement t as a record, but whatevs *)
let states : ('s, 'e) t -> 's list = function
  A (states, _, _, _) -> states
let start : ('s, 'e) t -> 's = function
  A (_, start, _, _) -> start
let delta : ('s, 'e) t -> ('s, 'e) Graph.t = function
  A (_, _, delta, _) -> delta
let accepting : ('s, 'e) t -> 's list = function
  A (_, _, _, accepting) -> accepting

(* take one step along the automata *)
let consume_symbol (init : 's) (s : 'e) (a : ('s, 'e) t) : 's list =
  let out_edges = (delta a) init in
  let fm = fun (e, v) -> if e == s then Some v else None in
    CCList.filter_map fm out_edges    

(* consumes a word *)
let rec consume (init : 's) (w : 'e list) (a : ('s, 'e) t) : 's list =
  match w with
    | [] -> []
    | s :: ss ->
      let out_states = consume_symbol init s a in
      let step_again = fun i -> consume i ss a in
        CCList.flat_map step_again out_states

(* containment in the language *)
let mem (w : 'e list) (a : ('s, 'e) t) : bool =
  let terminal_states = consume (start a) w a in
  let accepting = fun s -> List.mem s (accepting a) in
    CCList.exists accepting terminal_states

(* negation *)
let negate : ('s, 'e) t -> ('s, 'e) t = fun (A (l, s, d, acc)) ->
  let f = fun s -> not (List.mem s acc) in
    A (l, s, d, CCList.filter f acc)
  
(* some summary utilities *)
let summary (np : 's -> string) (ep : 'e -> string) (a : ('s, 'e) t) : string = match a with
  | A (l, s, d, f) ->
    let local_view = fun v ->
      let v' = np v in
      let d' = CCList.map (fun (e, v) -> "-{" ^ (ep e) ^ "}-> " ^ (np v)) (d v) in
        CCString.concat "\n\t" (v' :: d') in
    let start' = "Start:\n\t" ^ (np s) in
    let acc' =
      CCString.concat "\n\t" ("Accepting:" :: (CCList.map np f)) in
    let divider = "<==================================>" in
    CCString.concat "\n" (start' :: acc' :: divider :: (CCList.map local_view l))