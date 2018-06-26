(* we store proofs *)
type proof = Abstraction.proof

(* branches are effectively a sequence of edges, and describe an abstraction *)
type step = [
  | `Add of proof
  | `Merge of int * int * proof
  | `Generalize of int * proof
]

type branch = {
  abstraction : Abstraction.t;
  history : step list;
}

(* the default is super empty *)
let default : branch = {
  abstraction = [];
  history = [];
}

(* a heuristic assigns some value to a branch *)
module Heuristic = struct
  type t = branch -> int
  let default : t = fun b -> CCList.length b.history
end

(* our search is a heap maintaining branches *)
module Node = struct
  type t = int * branch
  (* ordering is all that's necessary to maintain frontier *)
  let leq (left : t) (right : t) : bool = (fst left) <= (fst right)
  (* getting a node is easy *)
  let of_branch (heuristic : Heuristic.t) : branch -> t = fun b ->
    (heuristic b, b)
  (* getting a branch from a node is even easier *)
  let to_branch : t -> branch = snd
end

(* so a history is really a worklist/frontier maintaining branches *)
module Frontier = CCHeap.Make(Node)
type t = Frontier.t

(* initializing a history just places the default branch *)
let init : t =
  Frontier.add Frontier.empty (Node.of_branch Heuristic.default default)

(* adding to the frontier requires a heuristic, but we have a default *)
let add ?(heuristic=Heuristic.default) (history : t) (b : branch) : t =
  let node = Node.of_branch heuristic b in
    Frontier.add history node

(* jsut a view to the top *)
let current : t -> branch option = fun h -> 
  Frontier.find_min h |> CCOpt.map Node.to_branch

(* pops the top element off, returns the resulting heap in addition *)
let pop : t -> (branch * t) option = fun h ->
  Frontier.take h
    |> CCOpt.map CCPair.swap
    |> CCOpt.map (CCPair.map1 Node.to_branch)

(* we'll extend branches during our search - this module defines the interface *)
module Extend = struct
  (* addition is the simplest *)
  let add : branch -> proof -> branch = fun b -> fun proof -> {
    abstraction = b.abstraction @ [proof];
    history = b.history @ [`Add proof];
  }
  (* for merge and generalize, we remove the proof at the associated indices *)
  let merge : branch -> int -> int -> proof -> branch = fun b -> fun l -> fun r -> fun proof -> {
    abstraction = b.abstraction
      |> CCList.mapi CCPair.make
      |> CCList.remove_assoc ~eq:(=) l
      |> CCList.remove_assoc ~eq:(=) r
      |> CCList.map snd
      |> (@) [proof];
    history = b.history @ [`Merge (l, r, proof)];
  }
  let generalize : branch -> int -> proof -> branch = fun b -> fun i -> fun proof -> {
    abstraction = b.abstraction
      |> CCList.mapi CCPair.make
      |> CCList.remove_assoc ~eq:(=) i
      |> CCList.map snd
      |> (@) [proof];
    history = b.history @ [`Generalize (i, proof)];
  }
end