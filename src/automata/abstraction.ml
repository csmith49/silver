(* edges are the same language as program automata *)
module Edge = struct
  type t = Program.Edge.t
end

(* nodes contain the relevant annotations, or possibly a list of annotations *)
module Node = struct
  type t = {
    annotation : AST.expr;
    cost : AST.expr;
  }
  type conjunction = t list
end

(* an abstraction is a list of annotated automata *)
type proof = (Node.t, Edge.t) Automata.t
type conjunction = (Node.conjunction, Edge.t) Automata.t
type t = proof list

(* given an abstraction, it is simple to add a new proof automata *)
let add (a : proof) (abs : t) : t = a :: abs

(* we really only care about computing the complement *)
(* we cannot use the typical intersection : tuples are not homogeneous objects *)
let lift_proof : proof -> conjunction = fun a -> {
    Automata.states = CCList.map CCList.pure a.Automata.states;
    start = [a.Automata.start];
    delta = Graph.map CCList.pure CCList.hd a.Automata.delta;
    accepting = CCList.map CCList.pure a.Automata.accepting;
  }

let conjoin (p : proof) (c : conjunction) : conjunction = {
    Automata.states = p.Automata.states
      |> CCList.flat_map (fun a -> CCList.map (fun rest -> a :: rest) c.Automata.states);
    start = p.Automata.start :: c.Automata.start;
    delta = Graph.map2 CCList.cons CCList.hd CCList.tl p.Automata.delta c.Automata.delta;
    accepting = p.Automata.accepting
      |> CCList.flat_map (fun a -> CCList.map (fun rest -> a :: rest) c.Automata.accepting);
  }

let rec complement : t -> conjunction option = function
  | [] -> None
  | a :: [] -> Some (a |> lift_proof |> Automata.negate)
  | a :: rest -> match complement rest with
    | Some abs -> let p = (a |> Automata.negate) in Some (conjoin p abs)
    | None -> None

(* and, we will need to check that the abstraction covers a program *)
(* the generation of counter-examples are important - these are Graph.paths *)
(* over _program_ edges and nodes *)
type answer =
  | Covers
  | Counterexample of (Program.Node.t, Program.Edge.t) Graph.Path.t

let covers (p : Program.t) (abs : t) : answer =
  match complement abs with
    | Some conjunct -> begin match Automata.get_word (Automata.intersect p conjunct) with
        | Some path -> Counterexample (Graph.Path.map fst path)
        | None -> Covers
      end
    | None -> begin match Automata.get_word p with
        | Some path -> Counterexample path
        | None -> Covers
      end