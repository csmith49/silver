(* we have an infinite symbol set, so we must represent transitions with sets *)
module Alphabet = struct
  (* ground constructors represent positive instances *)
  type 'a t =
    | Set of 'a list
    | Star
    (* negative instances use this recursive type constructor *)
    | Complement of 'a t

  (* if we somehow end up with nested complements, we wish to collapse them *)
  let rec simplify : 'a t -> 'a t = function
    | Complement (Complement s) -> simplify s
    | Complement (Set []) -> Star
    | Set [] -> Complement Star
    | _ as s -> s

  (* to ease construction later *)
  let lift : 'a -> 'a t = fun a -> Set [a]
  let of_list : 'a list -> 'a t = fun ss -> simplify (Set ss)

  (* printing *)
  let rec format ap f : 'a t -> unit = function
    | Star -> CCFormat.fprintf f "*"
    | Set ss -> CCFormat.fprintf f "@[<hv>%a@]" 
      (CCFormat.list ~sep:(CCFormat.return ",@ ") ap) ss
    | Complement s -> CCFormat.fprintf f "!{%a}" (format ap) s

  (* functional constructors / destructors *)
  let complement : 'a t -> 'a t = fun s -> simplify (Complement s)
  let ( ! ) : 'a t -> 'a t = fun s -> complement s

  let is_positive : 'a t -> bool = function
    | Set _ -> true
    | Star -> true
    | Complement _ -> false

  let is_empty : 'a t -> bool = function
    | Complement Star -> true
    | _ -> false
  
  let is_complete : 'a t -> bool = function
    | Star -> true
    | _ -> false

  let empty : 'a t = Complement Star

  (* intersection *)
  let intersect ?(a_eq = (=)) (left : 'a t) (right : 'a t) : 'a t = match left, right with
    | Star, _ -> right
    | _, Star -> left
    | Set ls, Set rs ->
      let basis = ls |> CCList.filter (fun l -> CCList.mem a_eq l rs) in
      of_list basis
    | Set _, Complement Star -> empty
    | Complement Star, Set _ -> empty
    | Set ls, Complement (Set rs) ->
      let basis = ls |> CCList.filter (fun l -> not (CCList.mem a_eq l rs)) in
      of_list basis
    | Complement (Set ls), Set rs ->
      let basis = rs |> CCList.filter (fun r -> not (CCList.mem a_eq r ls)) in
      of_list basis
    | Complement (Set ls), Complement (Set rs) ->
      Complement (Set (ls @ rs))
    | _ -> raise (Invalid_argument "Cannot intersect non-simplified sets")
  
  (* union defined in terms of intersection and complement *)
  let union ?(a_eq = (=)) (left : 'a t) (right : 'a t) : 'a t =
    ! (intersect ~a_eq:a_eq (! left) (! right))

  let set_union ?(a_eq = (=)) : 'a t list -> 'a t = function
    | [] -> empty
    | a :: [] -> a
    | a :: ss -> CCList.fold_left (union ~a_eq:a_eq) a ss

  (* casting back down to the base symbols *)
  let concretize : 'a t -> 'a option = function
    | Set [a] -> Some a
    | _ -> None

  (* equality assumes 'a contains countably many objects *)
  let rec eq ?(a_eq = (=)) (left : 'a t) (right : 'a t) : bool = match left, right with
    | Star, Star -> true
    | Complement l, Complement r -> eq ~a_eq:a_eq l r
    | Set ls, Set rs -> CCList.for_all (fun l -> CCList.mem a_eq l rs) ls
    | _ -> false
end

(* typical definition of a dfa *)
type ('s, 'a) t = {
  start : 's;
  states : 's list;
  final : 's list;
  (* we don't assume the transition relation is total *)
  delta : ('s, 'a Alphabet.t) Graph.t;
}

(* paths might contain sets of 'a or singleton 'a - we have different types to distinguish this *)
type ('s, 'a) path = ('s, 'a Alphabet.t) Graph.Path.t
type ('s, 'a) concrete_path = ('s, 'a) Graph.Path.t

(* if every label in the path is representing a singleton, we can concretize *)
let concretize : ('s, 'a) path -> ('s, 'a) concrete_path option = fun p ->
  let concretized = p 
    |> CCList.filter_map (fun (s, l, d) -> match Alphabet.concretize l with
        | Some l -> Some (s, l, d)
        | None -> None) in
  if (CCList.length concretized) = (CCList.length p) then Some concretized else None


(* we want to find words in the langauge defined by an automata *)
let find ?(s_eq = (=)) (dfa : ('s, 'a) t) : ('s, 'a) path option =
  Graph.bfs ~v_eq:s_eq [dfa.start] dfa.final dfa.delta

let find_concrete ?(s_eq = (=)) (dfa : ('s, 'a) t) : ('s, 'a) concrete_path option =
  CCOpt.Infix.(find ~s_eq:s_eq dfa >>= concretize)

(* we can convert a partial transition relation to a total one *)
let complete ?(s_eq = (=)) ?(a_eq = (=)) (dump : 's) (dfa : ('s, 'a) t) : ('s, 'a) t =
  let complete_state : 's -> ('s, 'a Alphabet.t) Graph.t = fun state ->
    let out_labels = state |> dfa.delta |> CCList.map fst in
    let out_coverage = out_labels |> Alphabet.set_union ~a_eq:a_eq in
    if Alphabet.is_complete out_coverage
      then fun _ -> []
      else Graph.of_edge ~v_eq:s_eq (state, Alphabet.(! out_coverage), dump) in
  {
    states = dump :: dfa.states;
    start = dfa.start;
    final = dfa.final;
    delta = CCList.fold_left Graph.merge dfa.delta (CCList.map complete_state dfa.states);
  }

(* negating a dfa only works if it has been completed - we don't enforce this with type safety *)
let negate ?(s_eq = (=)) (dfa : ('s, 'a) t) : ('s, 'a) t = {
  dfa with final = dfa.states |> CCList.filter (fun s -> not (CCList.mem s_eq s dfa.final));
}

(* a utility function for combining lists *)
let map2_cartesian (f : 'a -> 'b -> 'c) (left : 'a list) (right : 'b list) : 'c list =
  CCList.flat_map (fun l -> CCList.map (f l) right) left

(* general form of intersection *)
let intersect 
  ?(a_eq = (=)) 
  (f : 'x -> 'y -> 'z)
  (x : 'z -> 'x)
  (y : 'z -> 'y)
  (left : ('x, 'a) t) (right : ('y, 'a) t) : ('z, 'a) t =
  let merge = fun l -> fun r ->
    let intersection = Alphabet.intersect ~a_eq:a_eq l r in
    if Alphabet.is_empty intersection then None else Some intersection in
  {
    start = f left.start right.start;
    states = map2_cartesian f left.states right.states;
    final = map2_cartesian f left.final right.final;
    delta = Graph.map2 merge f x y left.delta right.delta;
  }

(* removes all unreachable states *)
let prune ?(s_eq = (=)) (dfa : ('s, 'a) t) : ('s, 'a) t = 
  let reachable = Graph.reachable ~v_eq:s_eq [dfa.start] dfa.delta in
  { dfa with
    states = dfa.states |> CCList.filter (fun s -> CCList.mem s_eq s reachable);
    final = dfa.final |> CCList.filter (fun s -> CCList.mem s_eq s reachable);
  }

(* printing *)
let rec format sf lf f : ('s, 'w) t -> unit = fun automata ->
  CCFormat.fprintf f "@[<v>Start: %a@;Final:@[<v 1>@;%a@]@;Edges:@[<v 1>@;%a@]"
    sf automata.start
    (CCFormat.list ~sep:(CCFormat.return "@ ") sf) automata.final
    (CCFormat.list ~sep:(CCFormat.return "@;") (format_local automata.delta sf lf)) automata.states
and format_local (g : ('s, 'w Alphabet.t) Graph.t) sf lf f : 's -> unit = fun state ->
  CCFormat.fprintf f "%a @[<hov>@,%a@]"
    sf state
    (CCFormat.list 
      ~sep:(CCFormat.return "@;") 
      (Graph.Path.format_short_step sf (Alphabet.format lf))) 
    (g state |> CCList.map (fun (lbl, dest) -> (state, lbl, dest)))
