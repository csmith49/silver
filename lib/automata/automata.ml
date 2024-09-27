module Program = Program
module Abstraction = Abstraction
module Cost = Cost
module DFA = DFA
module Graph = Graph

(* we have an infinite symbol set, so to complete our dfas we need more symbolic labels *)
module Symbol = struct
  (* we construct the powerset lattice over symbols *)
  type 'a t =
    | Singleton of 'a
    | Star
    | Complement of 'a list
    | Empty
  
  (* for printing *)
  let format af f : 'a t -> unit = function
    | Singleton a -> af f a
    | Star -> CCFormat.fprintf f "*"
    | Complement xs ->
      CCFormat.fprintf f "!{@[<hov 2>%a@]}" (CCFormat.list ~sep:(CCFormat.return ",@ ") af) xs
    | Empty -> CCFormat.fprintf f "()"

  (* assume left is a singleton - is it in the set described by right? *)
  let left_contains ?(s_eq = (=)) (left : 'a t) (right : 'a t) : bool = match left, right with
    | Singleton _, Star -> true
    | Singleton l, Singleton r -> s_eq l r
    | Singleton l, Complement rs -> not (CCList.mem ~eq:s_eq l rs)
    | _ -> false

  (* meet on the powerset lattice *)
  let intersect ?(s_eq = (=)) (left : 'a t) (right : 'a t) : 'a t = match left, right with
    | Empty, _ -> Empty
    | _, Empty -> Empty
    | Star, (_ as r) -> r
    | (_ as l), Star -> l
    | Singleton l, Singleton r -> if s_eq l r then Singleton l else Empty
    | Singleton l, Complement rs -> if (CCList.mem ~eq:s_eq l rs) then Empty else Singleton l
    | Complement ls, Singleton r -> if (CCList.mem ~eq:s_eq r ls) then Empty else Singleton r
    | Complement ls, Complement rs -> Complement (ls @ rs)

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
  
  let is_empty : 'a t -> bool = function
    | Empty -> true
    | _ -> false

  (* for map2 purposes *)
  let merge ?(s_eq = (=)) : 'a t -> 'a t -> 'a t option = fun l -> fun r ->
    let answer = intersect ~s_eq:s_eq l r in
    if is_empty answer then None else Some answer
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
let rec consume ?(l_eq = (=)) (start : 's) (word : 'w list) (automata : ('s, 'w) t) : 's list =
  match word with
    | [] -> [start]
    | l :: ls ->
      let next_states = consume_letter ~l_eq:l_eq l start automata in
      let step_again = fun state -> consume ~l_eq:l_eq state ls automata in
        CCList.flat_map step_again next_states

(* check to see if a word is accepted *)
let mem ?(s_eq = (=)) ?(l_eq = (=)) (word : 'w list) (automata : ('s, 'w) t) : bool =
  let terminal_states = consume ~l_eq:l_eq automata.start word automata in
  let accepting = fun state -> CCList.mem ~eq:s_eq state automata.final in
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

let complete ?(s_eq = (=)) (automata : ('s, 'w) t) (dump : 's) : ('s, 'w) t = 
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
  let not_final = fun state -> not (CCList.mem ~eq:s_eq state automata.final) in
  { automata with final = CCList.filter not_final automata.states; }

(* find a word in the language, if one exists *)
let find ?(s_eq = (=)) (automata : ('s, 'w) t) : ('s, 'w) path option =
  Graph.bfs ~v_eq:s_eq [automata.start] automata.final automata.delta

(* construct the intersection automata *)
let intersect ?(l_eq = (=)) (a : ('a, 'w) t) (b : ('b, 'w) t) : ('a * 'b, 'w) t = 
  {
    states = a.states
      |> CCList.flat_map (fun a -> CCList.map (CCPair.make a) b.states);
    start = (a.start, b.start);
    delta = Graph.map2 (Symbol.merge ~s_eq:l_eq) CCPair.make fst snd a.delta b.delta;
    final = a.final
      |> CCList.flat_map (fun a -> CCList.map (CCPair.make a) b.final);
  }

(* for printing *)
let rec format sf lf f : ('s, 'w) t -> unit = fun automata ->
  CCFormat.fprintf f "@[<v>Start: %a@;Final:@[<v 1>@;%a@]@;Edges:@[<v 1>@;%a@]"
    sf automata.start
    (CCFormat.list ~sep:(CCFormat.return "@ ") sf) automata.final
    (CCFormat.list ~sep:(CCFormat.return "@;") (format_local automata.delta sf lf)) automata.states
and format_local (g : ('s, 'w Symbol.t) Graph.t) sf lf f : 's -> unit = fun state ->
  CCFormat.fprintf f "%a @[<hov>@,%a@]"
    sf state
    (CCFormat.list 
      ~sep:(CCFormat.return "@;") 
      (Graph.Path.format_short_step sf (Symbol.format lf))) 
    (g state |> CCList.map (fun (lbl, dest) -> (state, lbl, dest)))

(* pruning just removes unreachable states *)
let prune ?(s_eq = (=)) : ('s, 'w) t -> ('s, 'w) t = fun automata -> 
  let reachable = Graph.reachable ~v_eq:s_eq [automata.start] automata.delta in {
    automata with 
      states = CCList.filter (fun state -> CCList.mem ~eq:s_eq state reachable) automata.states;
      final = CCList.filter (fun state -> CCList.mem ~eq:s_eq state reachable) automata.final;
  }