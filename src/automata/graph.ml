(* graphs are represented by the child relation *)
type ('v, 'e) t = 'v -> ('e * 'v) list

module Path = struct
  (* steps are effectively elements in the transition relation *)
  type ('v, 'e) step = 'v * 'e * 'v

  (* and paths are lists of steps *)
  type ('v, 'e) t = ('v, 'e) step list

  (* printer - need helper functions *)
  let rec to_string (vp : 'v -> string) (ep : 'e -> string) : ('v, 'e) t -> string = function
    | [] -> "ε"
    | (src, lbl, dest) :: [] ->
      (vp src) ^ "--{" ^ (ep lbl) ^ "}->" ^ (vp dest)
    | (src, lbl, _) :: rest ->
    (vp src) ^ "--{" ^ (ep lbl) ^ "}->" ^ (to_string vp ep rest)

  let rec format vf ef f : ('v, 'e) t -> unit = function
    | [] -> CCFormat.fprintf f "ε"
    | x :: xs ->
      CCFormat.fprintf f "@[<4>%a@;@[<v>%a@]@]" 
        (format_step vf ef) x
        (CCFormat.list ~sep:(CCFormat.return "@;") (format_short_step vf ef)) xs
  and format_step vf ef f : ('v, 'e) step -> unit = function
    (src, lbl, dest) -> CCFormat.fprintf f "@[%a ~{ %a }~@ %a@]" vf src ef lbl vf dest
  and format_short_step vf ef f : ('v, 'e) step -> unit = function
    (_, lbl, dest) -> CCFormat.fprintf f "~{ %a }~ %a" ef lbl vf dest



  (* convert path to list of labels *)
  let rec to_word : ('v, 'e) t -> 'e list = function
    | [] -> []
    | (_, lbl, _) :: rest -> lbl :: (to_word rest)

  (* convert path to list of states - note the lack of double-counting *)
  let rec to_states : ('v, 'e) t -> 'v list = function
    | [] -> []
    | (src, _, dest) :: [] -> [src ; dest]
    | (src, _, _) :: rest -> src :: (to_states rest)
  
  (* concat a step at the end of a path *)
  let extend : ('v, 'e) t -> ('v, 'e) step -> ('v, 'e) t = 
    fun path -> fun step -> path @ [step]

  (* convert a step to a really short path *)
  let of_step : ('v, 'e) step -> ('v, 'e) t = fun s -> [s]

  (* check if a path visits any state more than once *)
  let has_loop ?(v_eq = (=)) : ('v, 'e) t -> bool = fun path ->
    let rec contains_duplicates vertices = match vertices with
      | [] -> false
      | v :: vs -> if CCList.mem ~eq:v_eq v vs
        then true 
        else contains_duplicates vs in
    path |> to_states |> contains_duplicates

  (* mapping a path happens over states *)
  let rec map (f : 'v -> 'w) : ('v, 'e) t -> ('w, 'e) t = function
    | [] -> []
    | (src, lbl, dest) :: rest ->
      (f src, lbl, f dest) :: (map f rest)
end

(* construct a graph from a path *)
let of_path ?(v_eq = (=)) : ('v, 'e) Path.t -> ('v, 'e) t = fun path -> fun v -> path
  |> CCList.filter_map (fun (src, lbl, dest) -> if v_eq src v then Some (lbl, dest) else None)

(* path manipulations with graphs *)
let step (v : 'v) (g : ('v, 'e) t) : ('v, 'e) Path.step list = 
  v |> g |> CCList.map (fun (lbl, dest) -> (v, lbl, dest))

let extend (path : ('v, 'e) Path.t) (g : ('v, 'e) t) : ('v, 'e) Path.t list = path
  |> Path.to_states |> CCList.last_opt (* get the last state *)
  |> CCOption.map (fun v -> step v g) |> CCOption.to_list |> CCList.flatten (* turn to list of steps *)
  |> CCList.map (Path.extend path) (* and extend *)

(* compute the first path (if one exists) from source to dest *)
let bfs ?(v_eq = (=)) (source : 'v list) (dest : 'v list) (g : ('v, 'e) t) : ('v, 'e) Path.t option =
  (* use an aux function that maintains paths *)
  let rec aux = fun paths ->
    (* find if anything is currently reaching the destination *)
    let reaches_dest = fun path -> path
      |> Path.to_states |> CCList.last_opt 
      |> CCOption.exists (fun v -> CCList.mem ~eq:v_eq v dest) in
    match CCList.find_opt reaches_dest paths with
      | Some path -> Some path
      | None ->
        (* extend the path and filter those with loops *)
        let loop_free_paths = paths
          |> CCList.flat_map (fun path -> extend path g)
          |> CCList.filter (fun path -> not (Path.has_loop ~v_eq:v_eq path)) in
        (* maybe recurse *)
        if CCList.is_empty loop_free_paths then None else aux loop_free_paths in
  (* generate the initial paths out of source *)
  let init_paths = source |> CCList.flat_map (fun v -> step v g) |> CCList.map Path.of_step in
    aux init_paths

(* compute all loop-free paths from source to dest *)
let bfs_list ?(v_eq = (=)) (source : 'v list) (dest : 'v list) (g : ('v, 'e) t) : ('v, 'e) Path.t list =
  (* aux function that operates over paths *)
  let rec aux = fun paths ->
    (* we need to check if paths have reached the destination *)
    let reaches_dest = fun path -> path
      |> Path.to_states |> CCList.last_opt
      |> CCOption.exists (fun v -> CCList.mem ~eq:v_eq v dest) in
    (* split the paths into those reaching the destination and those that need to be extended *)
    let finished, ongoing = CCList.partition reaches_dest paths in
    (* extend ongoing and filter out paths with loops *)
    let ongoing = ongoing
      |> CCList.flat_map (fun path -> extend path g)
      |> CCList.filter (fun path -> not (Path.has_loop ~v_eq:v_eq path)) in
    (* recurse if necessary *)
    if CCList.is_empty ongoing then finished else finished @ (aux ongoing) in
  (* generate initial paths out of source *)
  let init_paths = source |> CCList.flat_map (fun v -> step v g) |> CCList.map Path.of_step in
    aux init_paths

(* compute the set of states reachable from source *)
let rec reachable ?(v_eq = (=)) (source : 'v list) (g : ('v, 'e) t) : 'v list =
  let step_reachable = source
    |> CCList.flat_map (fun v -> step v g)
    |> CCList.map (fun (_, _, dest) -> dest) in
  let unseen_states = 
    CCList.filter (fun v -> not (CCList.mem ~eq:v_eq v source)) step_reachable in
  if CCList.is_empty unseen_states then source else reachable (source @ unseen_states) g

(* to help divine the og structure, maps need inverses *)
let map (f : 'v -> 'w) (f' : 'w -> 'v) (g : ('v, 'e) t) : ('w, 'e) t = fun w -> w
  |> f' |> g |> CCList.map (fun (lbl, dest) -> (lbl, f dest))

(* and map2 needs inverse projections, as well as an edge combining operation *)
let map2 
  (e : 'e -> 'e -> 'e option) 
  (f : 'a -> 'b -> 'c) (x : 'c -> 'a) (y : 'c -> 'b) 
  (g : ('a, 'e) t) (h : ('b, 'e) t) : ('c, 'e) t = fun c ->
    let a_edges = c |> x |> g in
    let b_edges = c |> y |> h in a_edges
      |> CCList.flat_map (fun  a -> CCList.map (CCPair.make a) b_edges)
      |> CCList.filter_map (fun ((le, a), (re, b)) -> match e le re with
          | Some edge -> Some (edge, f a b)
          | None -> None)

(* the simplest instantiation of map2 is the product construction *)
let product ?(e_eq = (=)) (g : ('v, 'e) t) (h : ('w, 'e) t) : ('v * 'w, 'e) t =
  let e = fun l -> fun r -> if e_eq l r then Some l else None in
  map2 e CCPair.make fst snd g h

(* minor construction utilities *)
let of_edge ?(v_eq = (=)) (edge : 'v * 'e * 'v) : ('v, 'e) t =
  let src, lbl, dest = edge in fun v -> if v_eq v src then [(lbl, dest)] else []

let merge (g : ('v, 'e) t) (h : ('v, 'e) t) : ('v, 'e) t = fun v -> (g v) @ (h v)

(* merging staes makes two states be considered equivalent for purposes of out edges *)
let merge_states ?(v_eq = (=)) (left : 'v) (right : 'v) (g : ('v, 'e) t) : ('v, 'e) t = fun n ->
  if (v_eq n right) || (v_eq n left) then (g left) @ (g right) else g n

let pinch ?(v_eq = (=)) (states : 'v list) (g : ('v, 'e) t) : ('v, 'e) t = match states with
  | [] -> g
  | x :: [] -> g
  | x :: xs ->
    CCList.fold_left (fun graph -> fun state -> merge_states ~v_eq:v_eq state x graph) g xs

(* place a graph over another (h ontop of g, obscuring edges equivalent via e_eq) *)
let overlay ?(v_eq = (=)) ?(e_eq = (=)) (g : ('v, 'e) t) (h : ('v, 'e) t) : ('v, 'e) t = fun v ->
  let eq (el, nl) (er, nr) = (v_eq nl nr) = (e_eq el er) in
  let h_edges = v |> h in
  let g_edges = v |> g |> CCList.filter (fun e -> not (CCList.mem ~eq:eq e h_edges)) in
    h_edges @ g_edges

(* mapping edges is sooooo much easier than states - no inverse needed *)
let map_edge (f : 'e -> 'f) (g : ('v, 'e) t) : ('v, 'f) t = fun n -> n
  |> g
  |> CCList.map (CCPair.map_fst f)

(* we should be able to tell when a loop exists between two sets of states *)
let loop_free ?(v_eq = (=)) (source : 'v list) (dest : 'v list) : ('v, 'e) t -> bool = fun g ->
  (* aux function iterates over paths *)
  let rec aux = fun paths ->
    (* check for loops *)
    if CCList.exists (Path.has_loop ~v_eq:v_eq) paths then false else
    (* see what we can drop *)
    let reaches_dest = fun path -> path
      |> Path.to_states |> CCList.last_opt
      |> CCOption.exists (fun v -> CCList.mem ~eq:v_eq v dest) in
    (* filter out paths reaching the state and extend *)
    let ongoing = paths
      |> CCList.filter reaches_dest
      |> CCList.flat_map (fun path -> extend path g) in
    if CCList.is_empty ongoing then true else aux ongoing
  in let init_paths = source |> CCList.flat_map (fun v -> step v g) |> CCList.map Path.of_step in
    aux init_paths
    