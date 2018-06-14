(* edges are the same language as program automata *)
module Label = Program.Label

(* states contain the relevant annotations, or possibly a list of annotations *)
module State = struct
  type t = {
    id : Name.t;
    tags : Program.Tag.t list;
    (* if we're generating interpolants lazily, these may not be filled in *)
    annotation : AST.expr option;
    cost : AST.expr option;
  }

  (* printing *)
  let to_string : t -> string = fun s -> Name.to_string s.id

  (* comparison just the polymorphic default *)
  let eq = (=)
end

(* a proof is therefore just an automata with states/labels as above *)
type proof = (State.t, Label.t) Automata.t

(* and an abstraction is a list of proofs *)
type t = proof list

(* alias for the following module *)
type abstraction = t

(* we have an intermediate type - never stored, just constructed, tested against, and discarded *)
module Conjunction = struct
  (* tuples are not homogeneous, so we use lists instead *)
  type t = (State.t list, Label.t) Automata.t

  (* lift a proof to a conjunction - corresponds to singleton list construction *)
  let lift (proof : proof) : t = {
    Automata.states = CCList.map CCList.pure proof.Automata.states;
    start = [proof.Automata.start];
    delta = Graph.map CCList.pure CCList.hd proof.Automata.delta;
    final = CCList.map CCList.pure proof.Automata.final;
  }

  (* and add a proof to a conjunction - this might be thought of as cons *)
  let conjoin (proof : proof) (c : t) : t = {
    Automata.states = proof.Automata.states
      |> CCList.flat_map (fun a -> CCList.map (CCList.cons a) c.Automata.states);
    start = proof.Automata.start :: c.Automata.start;
    delta = Graph.map2 CCList.cons CCList.hd CCList.tl proof.Automata.delta c.Automata.delta;
    final = proof.Automata.final
      |> CCList.flat_map (fun a -> CCList.map (CCList.cons a) c.Automata.final);
  }

  (* construct a conjunction - if possible - from an abstraction *)
  let rec of_abstraction : abstraction -> t option = function
    | [] -> None (* no clear way to make empty conjunction *)
    | proof :: [] -> Some (lift proof)
    | proof :: rest -> match of_abstraction rest with
      | Some conjunct -> Some (conjoin proof conjunct)
      | None -> None (* this case should never happen *)

  (* printing *)
  let to_string : t -> string =
    let slist_to_string (ss : State.t list) = CCList.map State.to_string ss |> CCString.concat " | "
    in Automata.to_string slist_to_string Program.Label.to_string
end

(* printing just constructs the conjunction and goes from there *)
let to_string : t -> string = fun abs -> match Conjunction.of_abstraction abs with
  | Some conjunct -> Conjunction.to_string conjunct
  | None -> "EMPTY"

(* initial construction *)
let init = []

(* given an abstraction, it is simple to add a new proof automata *)
let add (a : proof) (abs : t) : t = a :: abs

(* to compute the complement, we convert to a conjunction and negate *)
let complement (abs : t) : Conjunction.t option =
  match Conjunction.of_abstraction abs with
    | Some conjunct -> Some (Automata.negate conjunct)
    | None -> None

(* and, we will need to check that the abstraction covers a program *)
(* the generation of counter-examples are important - these are paths *)
(* over _program_ states and labels *)
type answer =
  | Covers
  | Counterexample of Program.path

 module Intersection = struct
  module State = struct
    type t = Program.State.t * State.t list

    (* lifting eq up to the automata constructed in covers *)
    let rec lex_eq (eq : 'a -> 'a -> bool) (left : 'a list) (right : 'a list) : bool = match left, right with
    | x :: xs, y :: ys ->
      if eq x y then lex_eq eq xs ys else false
    | [], [] -> true
    | _ -> false

    (* and lifting eq over pairs *)
    let pair_eq (l_eq : 'a -> 'a -> bool) (r_eq : 'b -> 'b -> bool) (left : 'a * 'b) (right : 'a * 'b) : bool =
      match left, right with (a, b), (a', b') -> (l_eq a a') && (r_eq b b')

    (* constructing the eq from primitives *)
    let eq = pair_eq Program.State.eq (lex_eq State.eq)

    let to_string : t -> string = fun (s, ss) ->
      let s' = Program.State.to_string s in
      let ss' = CCList.map State.to_string ss in
        CCString.concat " | " (s' :: ss')
  end

  module Label = Program.Label

  type t = (State.t, Label.t) Automata.t

  let to_string : t -> string = Automata.to_string State.to_string Label.to_string
 end

(* check if the program is covered by the abstraction *)
let vprint verbose msg = if verbose then print_endline msg else ()

let covers ?(verbose=false) (p : Program.t) (abs : t) : answer =
  let vp = vprint verbose in
  let _ = vp "[COVERING] Generating complement..." in
  let comp = complement abs in
  let _ = vp "[COVERING] Complement automata is: " in
  match comp with
    | Some conjunct ->
      let _ = vp (Conjunction.to_string conjunct) in
      let _ = vp "[COVERING] Computing intersection..." in
      let intersection = Automata.intersect p conjunct 
        |> Automata.prune ~s_eq:Intersection.State.eq in
      let _ = vp "[COVERING] Intersection is: " in
      let _ = vp (Intersection.to_string intersection) in
      let _ = vp "[COVERING] Finding path in intersection..." in
      let word = Automata.find ~s_eq:Intersection.State.eq intersection in
      begin match word with
        | Some path -> Counterexample (Graph.Path.map fst path)
        | None -> Covers
      end
    | None -> 
      let _ = vp "UNIVERSE\n[COVERING] No abstraction. Finding program path..." in
      begin match Automata.find ~s_eq:Program.State.eq p with
        | Some path -> Counterexample path
        | None -> Covers
      end

(* given a path we know is correct, we can build a proof *)
let of_path : Program.path -> proof = fun p ->
  let path = Graph.Path.map (fun n -> {
      State.id = n.Program.State.id;
      tags = n.Program.State.tags;
      annotation = None;
      cost = None;
    }) p in
  let states = Graph.Path.to_states path in
  {
    Automata.states = states;
    start = CCList.hd states;
    delta = Graph.of_path ~v_eq:State.eq path;
    final = [states |> CCList.last_opt |> CCOpt.get_exn];
  }