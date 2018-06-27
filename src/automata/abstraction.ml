(* edges are the same language as program automata *)
module Label = Program.Label

(* states contain the relevant annotations, or possibly a list of annotations *)
module State = struct
  type t = {
    id : Name.t;
    tags : Program.Tag.t list;
    (* if we're generating interpolants lazily, these may not be filled in *)
    annotation : AST.expr option;
  }

  (* printing *)
  let format f : t -> unit = fun s ->
    let s' = {
      Program.State.id = s.id;
      tags = s.tags;
    } in
    Program.State.format f s'

  let to_string : t -> string = fun s -> CCFormat.to_string format s

  (* comparison just the polymorphic default *)
  let eq (left : t) (right : t) : bool = (left.id, left.tags) = (right.id, right.tags)

  let to_program_state : t -> Program.State.t = fun s ->
  {
    Program.State.id = s.id;
    tags = s.tags;
  }
  let of_program_state : Program.State.t -> t = fun s -> {
    id = s.Program.State.id;
    tags = s.Program.State.tags;
    annotation = None;
  }

  (* canonical dump state *)
  let dump : t = {
    id = Name.of_string "dump";
    tags = [];
    annotation = None;
  }
end

(* a proof is therefore just an automata with states/labels as above *)
type proof_automata = (State.t, Label.t) DFA.t
type proof = {
  automata : proof_automata;
  cost : Cost.t;
}

let lift (f : proof_automata -> proof_automata) : proof -> proof = fun p -> {
  p with automata = f p.automata;
}

let to_dfa : proof -> proof_automata = fun p -> p.automata
let to_cost : proof -> Cost.t = fun p -> p.cost

let loop_free : proof -> bool = fun pf ->
  DFA.loop_free ~s_eq:State.eq pf.automata

(* and an abstraction is a list of proofs *)
type t = proof list

(* alias for the following module *)
type abstraction = t

(* negates every automata in the language *)
let negate : t -> t = fun abs -> CCList.map (fun p -> 
  p
  |> lift (DFA.complete ~s_eq:State.eq ~a_eq:Label.eq State.dump)
  |> lift (DFA.negate ~s_eq:State.eq)) abs

(* we have an intermediate type - never stored, just constructed, tested against, and discarded *)
module Conjunction = struct
  (* tuples are not homogeneous, so we use lists instead *)
  type t = (State.t list, Label.t) DFA.t

  (* lift a proof to a conjunction - corresponds to singleton list construction *)
  let lift (p : proof) : t = 
    let proof = lift (DFA.complete ~s_eq:State.eq ~a_eq:Label.eq State.dump) p in
      {
        DFA.states = CCList.map CCList.pure proof.automata.DFA.states;
        start = [proof.automata.DFA.start];
        delta = Graph.map CCList.pure CCList.hd proof.automata.DFA.delta;
        final = CCList.map CCList.pure proof.automata.DFA.final;
      }

  (* and add a proof to a conjunction - this might be thought of as cons *)
  let conjoin (p : proof) (c : t) : t = 
    let proof = DFA.complete ~s_eq:State.eq ~a_eq:Label.eq State.dump p.automata in
    DFA.intersect ~a_eq:Label.eq CCList.cons CCList.hd CCList.tl proof c

  (* construct a conjunction - if possible - from an abstraction *)
  let rec of_abstraction : abstraction -> t option = function
    | [] -> None (* no clear way to make empty conjunction *)
    | proof :: [] -> Some (lift proof)
    | proof :: rest -> match of_abstraction rest with
      | Some conjunct -> Some (conjoin proof conjunct)
      | None -> None (* this case should never happen *)

  let eq = CCList.equal State.eq

  (* printing *)
  let format f : t -> unit = fun c ->
    CCFormat.fprintf f "%a"
      (DFA.format 
        (CCFormat.list ~sep:(CCFormat.return " | ") State.format) 
        Label.format)
      c
  let to_string : t -> string = CCFormat.to_string format
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
  abs |> negate |> Conjunction.of_abstraction

(* and, we will need to check that the abstraction covers a program *)
(* the generation of counter-examples are important - these are paths *)
(* over _program_ states and labels *)
type answer =
  | Covers
  | Counterexample of Program.path
  | Unknown

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

    (* printing *)
    let format f : t -> unit = fun (s, ss) ->
      CCFormat.fprintf f "%a | %a"
        Program.State.format s
        (CCFormat.list ~sep:(CCFormat.return " | ") State.format) ss
    let to_string : t -> string = CCFormat.to_string format
  end

  module Label = Program.Label

  type t = (State.t, Label.t) DFA.t

  (* printing *)
  let format f : t -> unit = fun i ->
    CCFormat.fprintf f "%a" (DFA.format State.format Label.format) i
  let to_string : t -> string = CCFormat.to_string format
 end

(* check if the program is covered by the abstraction *)

let covers ?(verbose=false) (p : Program.t) (abs : t) : answer =
  let _ = if verbose then CCFormat.printf "@[[COVERING] Generating complement...@]@;" else () in
  let comp = complement abs |> CCOpt.map (DFA.prune ~s_eq:Conjunction.eq) in
  match comp with
    | Some conjunct ->
      let _ = if verbose then 
        CCFormat.printf "@[[COVERING] Complement automata is:@;%a@]@;" Conjunction.format conjunct 
        else () in
      let _ = if verbose then CCFormat.printf "@[[COVERING] Computing intersection...@]@;" else () in
      let intersection = DFA.intersect ~a_eq:Label.eq CCPair.make fst snd p conjunct 
        |> DFA.prune ~s_eq:Intersection.State.eq in
      let _ = if verbose then CCFormat.printf
        "@[[COVERING] Intersection is:@;%a@]@;"
        Intersection.format intersection else () in
      let _ = if verbose then CCFormat.printf "@[[COVERING] Finding path in intersection...@]@;" in
      let word = DFA.find ~s_eq:Intersection.State.eq intersection in
      begin match word with
        | Some path -> begin match DFA.concretize (Graph.Path.map fst path) with
            | Some path -> Counterexample path
            | None -> Unknown
          end
        | None -> Covers
      end
    | None -> 
      let _ = if verbose then CCFormat.printf
        "@[[COVERING] Complement automata is:@;Universe@;[COVERING] No abstraction. Finding program path..@].@;" else () in
      begin match DFA.find ~s_eq:Program.State.eq p with
        | Some path -> begin match DFA.concretize path with
            | Some path -> Counterexample path
            | None -> Unknown
          end
        | None -> Covers
      end

(* given a path we know is correct, we can build a proof *)
(* these states should be made disjoint *)
let of_path : Program.path -> proof = fun path ->
  let state_map = path
    |> Graph.Path.to_states
    |> CCList.mapi (fun i -> fun s -> 
        let s' = {
          State.id = Name.extend_by_int s.Program.State.id i;
          tags = s.Program.State.tags;
          annotation = None;
        } in
        (s, s')) in
  let path = Graph.Path.map (fun s -> CCList.assoc ~eq:Program.State.eq s state_map) path in
  let states = Graph.Path.to_states path in
  let automata = {
    DFA.states = states;
    start = CCList.hd states;
    delta = Graph.map_edge DFA.Alphabet.lift (Graph.of_path ~v_eq:State.eq path);
    final = [states |> CCList.last_opt |> CCOpt.get_exn];
  } in
  let cost = path |> Graph.Path.to_word
    |> CCList.filter_map (fun w -> match w with
        | Program.Label.Concrete c -> Some c.Program.Label.cost
        | _ -> None)
    |> CCList.fold_left Cost.add Cost.zero
    |> Cost.simplify in
  {
    automata = automata;
    cost = cost;
  }

(* printing - we just go proof by proof *)
let format f : t -> unit = function
  | [] -> CCFormat.fprintf f "EMPTY"
  | abs ->
    CCFormat.fprintf f "@[<v>%a@;@]"
      (CCFormat.list 
        ~sep:(CCFormat.return "@;----@;") 
        (DFA.format State.format Label.format))
      (abs |> CCList.map to_dfa)