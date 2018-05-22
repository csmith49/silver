(* the machinery necessary for representing program automata *)
open Name.Infix

module Edge = struct
  type t =
    | Assume of AST.expr
    | Assign of AST.id * AST.expr
    | Draw of AST.id * AST.expr

  let to_string : t -> string = function
    | Assume e -> AST.expr_to_string e
    | Assign (i, e) ->
      let i' = AST.id_to_string i in
      let e' = AST.expr_to_string e in
        i' ^ " = " ^ e'
    | Draw (i, e) ->
      let i' = AST.id_to_string i in
      let e' = AST.expr_to_string e in
        i' ^ " ~ " ^ e'
end

module Node = struct
  type t = N of Name.t

  let to_name : t -> Name.t = function N n -> n

  let to_string : t -> string = fun n -> Name.to_string (to_name n)

  let counter = ref 0

  let extend (n : t) (s : string) : t =
    let i = !counter in
    let _ = counter := i + 1 in
    match n with
      N x -> N (x <+ (string_of_int i) <+ s)
  
  let of_string : string -> t = fun s -> N (Name.of_string s)
end

type t = (Node.t, Edge.t) Automata.t

(* a utility for later *)
let path_to_string : (Node.t, Edge.t) Graph.Path.t -> string =
  Graph.Path.pp Node.to_string Edge.to_string
let summary : t -> string = Automata.summary Node.to_string Edge.to_string


let rec graph_of_ast (ast : AST.t) (n : Node.t) : Node.t * (Node.t, Edge.t) Graph.t = match ast with
  | AST.Assign (i, e) ->
    let fresh_n = Node.extend n "assign" in
    let fresh_edge = Edge.Assign (i, e) in
    let delta = fun s -> if s = fresh_n then [(fresh_edge, n)] else [] in
      (fresh_n, delta)
  | AST.Draw (i, e) ->
    let fresh_n = Node.extend n "draw" in
    let fresh_edge = Edge.Draw (i, e) in
    let delta = fun s -> if s = fresh_n then [(fresh_edge, n)] else [] in
      (fresh_n, delta)
  | AST.ITE (b, l, r) ->
    let (ln, lg) = graph_of_ast l n in
    let (rn, rg) = graph_of_ast r n in
    let fresh_n = Node.extend n "ite" in
    let true_edge = Edge.Assume b in
    let false_edge = Edge.Assume (AST.UnaryOp (Operation.Defaults.not_, b)) in
    let delta = (fun s ->
      let old_edges = (lg s) @ (rg s) in
      if s = fresh_n then [(true_edge, ln); (false_edge, rn)] @ old_edges else old_edges) in
        (fresh_n, delta)
  | AST.While (b, e) ->
    let fresh_n = Node.extend n "while" in
    let (en, eg) = graph_of_ast e fresh_n in
    let loop_edge = Edge.Assume b in
    let exit_edge = Edge.Assume (AST.UnaryOp (Operation.Defaults.not_, b)) in
    let delta = (fun s ->
      let old_edges = eg s in
      if s = fresh_n then [(loop_edge, en); (exit_edge, n)] @ old_edges else old_edges) in
        (fresh_n, delta)
  | AST.Block xs -> begin match xs with
      | [] ->
        let delta = fun _ -> [] in
          (n, delta)
      | x :: rest ->  
        let (rest_n, rest_g) = graph_of_ast (AST.Block rest) n in
        let (xn, xg) = graph_of_ast x rest_n in
        let delta = (fun s -> (xg s) @ (rest_g s)) in
          (xn, delta)
    end

(* using the graph construction, we can now build up the program automata *)
let of_ast : AST.t -> t = fun ast -> 
  let final = Node.of_string "finish" in
  let (init, delta) = graph_of_ast ast final in
  {
    Automata.states = 
      CCList.sort_uniq Pervasives.compare (Graph.reachable [init] delta);
    start = init;
    delta = delta;
    accepting = [final];
  }
