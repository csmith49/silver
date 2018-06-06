open CCOpt.Infix

(* a graph is represented by the successor function *)
type ('v, 'e) t = 'v -> ('e * 'v) list

module Path = struct
  (* while paths are lists of v --e-> v tuples *)
  type ('v, 'e) step = ('v * 'e * 'v)

  type ('v, 'e) t = ('v, 'e) step list

  (* printing depends on the printing for 'v and 'e - provided, we can make a printer *)
  let pp (vertex_to_string : 'v -> string) (edge_to_string : 'e -> string) : ('v, 'e) t -> string =
    let rec print = fun p -> match p with
      | [] -> "ε"
      | (s, l, d) :: [] -> (vertex_to_string s) ^ " --(" ^ (edge_to_string l) ^ ")-> " ^ (vertex_to_string d)
      | (s, l, _) :: rest -> (vertex_to_string s) ^ " --(" ^ (edge_to_string l) ^ ")-> " ^ (print rest)
      in print

  (* if we just want the sequence of statements, we're in luck *)
  let to_word (p : (_, 'e) t) : 'e list = CCList.map (fun (_, l,_) -> l) p
  
  (* getting the states is just as easy *)
  let rec to_states (p : ('v, _) t) : 'v list = match p with
    | [] -> []
    | (s, l, d) :: [] -> [s; d]
    | (s, l, _) :: rest -> s :: (to_states rest)

  (* we really should represent paths backwards, but that's confusing *)
  let extend (p : ('v, 'e) t) (e : ('v, 'e) step) : ('v, 'e) t = p @ [e]

  (* of course, a step is basically a mini path with a diff. type to enforce incrementality *)
  let of_step : ('v, 'e) step -> ('v, 'e) t = fun s -> [s]

  (* we can tell if a path loops by checking for duplication in the states *)
  let has_loop (p : ('v, _) t) : bool =
    let rec contains_duplicates : 'a list -> bool = function
      | [] -> false
      | x :: xs -> if List.mem x xs then true else contains_duplicates xs
    in p |> to_states |> contains_duplicates

  (* mapping happens over states *)
  let map (f : 'v -> 'w) (p : ('v, 'e) t) : ('w, 'e) t =
    let map_step = fun (s, l, d) -> (f s, l, f d) in
      CCList.map map_step p
end

(* we can also think of paths as graphs in a very natural way *)
let of_path (p : ('v, 'e) Path.t) : ('v, 'e) t = fun v ->
  CCList.filter_map (fun (s, l, d) -> if v = s then Some (l, d) else None) p

(* functions over graphs must be structure-preserving: when we map, we must be able to invert *)
(* the correctness of the inversion is left to the user - there is no guarantee *)
let map (f : 'v -> 'n) (h : 'n -> 'v) (g : ('v, 'e) t) : ('n, 'e) t = fun n -> 
  n |> h |> g |> CCList.map (CCPair.map2 f)

(* for map2, we need projections to the components of the preimage *)
let map2 (f : 'a -> 'b -> 'c) (x : 'c -> 'a) (y : 'c -> 'b) (g : ('a, 'e) t) (h : ('b, 'e) t) : ('c, 'e) t = fun n ->
  let a_edges = n |> x |> g in let b_edges = n |> y |> h in a_edges
    |> CCList.flat_map (fun a -> CCList.map (fun b -> (a, b)) b_edges)
    |> CCList.filter_map (fun ((le, a), (re, b)) -> if le = re then Some (le, f a b) else None)

(* the simplest instantiation of map2 just pairs up the result *)
let product (g : ('v, 'e) t) (h : ('n, 'e) t) : ('v * 'n, 'e) t =
  map2 (fun x -> fun y -> (x, y)) fst snd g h

(* utility-wise, we really only require bfs *)
(* this requires a few helper functions *)
let step (n : 'v) (g : ('v, 'e) t) : ('v, 'e) Path.step list =
  n |> g |> CCList.map (fun (l, d) -> (n, l, d))

let extend_path (p : ('v, 'e) Path.t) (g : ('v, 'e) t) : ('v, 'e) Path.t list = p
  |> Path.to_states |> CCList.last_opt (* get the last state *)
  |> CCOpt.map (fun n -> step n g) |> CCOpt.to_list |> CCList.flatten (* turn to list of steps *)
  |> CCList.map (Path.extend p) (* and extend *)

(* bfs extends paths until it finds one reaching a destination *)
(* paths with loops are dropped *)
let bfs (source : 'v list) (dest : 'v list) (g : ('v, 'e) t) : ('v, 'e) Path.t option =
  (* we use a recursive auxillary function that maintains paths *)
  let rec aux : ('v, 'e) Path.t list -> ('v, 'e) Path.t option = fun ps ->
    (* find if anything is currently reaching the destination *)
    let reaches_dest: ('v, 'e) Path.t -> bool = fun p -> p
      |> Path.to_states |> CCList.last_opt |> CCOpt.exists (fun n -> List.mem n dest) in
    match CCList.find_opt reaches_dest ps with
      | Some p -> Some p
      | None ->
        (* extend the paths and filter those with loops *)
        let loop_free_paths = ps
          |> CCList.flat_map (fun p -> extend_path p g)
          |> CCList.filter (fun p -> not (Path.has_loop p)) in
        (* maybe recurse *)
        if CCList.is_empty loop_free_paths then None else aux loop_free_paths in
  (* generate the initial paths from source *)
  let init_paths = source |> CCList.flat_map (fun n -> step n g) |> CCList.map Path.of_step in
    (* and do the thing *)
    aux init_paths

(* we also care about some minor reachability *)
let rec reachable (init : 'v list) (g  : ('v, _) t) : 'v list =
  let step_reachable = init
    |> CCList.flat_map (fun n -> step n g)
    |> CCList.map (fun (_, _, d) -> d) in
  let unseen_states = CCList.filter (fun n -> not (List.mem n init)) step_reachable in
  if CCList.is_empty unseen_states then init else reachable (init @ unseen_states) g