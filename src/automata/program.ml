(* the machinery necessary for representing program automata *)
open Name.Infix

type edge =
  | Assume of AST.expr
  | Assign of AST.id * AST.expr
  | Draw of AST.id * AST.expr

type node =
  N of Name.t

(* some basic printing *)
let edge_to_string : edge -> string = function
  | Assume e -> AST.expr_to_string e
  | Assign (i, e) ->
    let i' = AST.id_to_string i in
    let e' = AST.expr_to_string e in
      i' ^ " = " ^ e'
  | Draw (i, e) ->
    let i' = AST.id_to_string i in
    let e' = AST.expr_to_string e in
      i' ^ " ~ " ^ e'

let node_to_string : node -> string = function
  N n -> Name.to_string n

(* we will need to make fresh nodes all the time *)
let node_counter = ref 0
let extend_node (n : node) (s : string) : node =
  let i = !node_counter in
  let _ = node_counter := !node_counter + 1 in
  match n with
    N x -> N (x <+ (string_of_int i) <+ s)

let name_of_node : node -> Name.t = function N n -> n

type t = (node, edge) Automata.t

(* a utility for later *)
let path_to_string : (node, edge) Automata.Graph.path -> string = 
  Automata.Graph.path_to_string node_to_string edge_to_string
let summary : t -> string = Automata.summary node_to_string edge_to_string


let rec graph_of_ast (ast : AST.t) (n : node) : node * (node, edge) Automata.Graph.t = match ast with
  | AST.Assign (i, e) ->
    let fresh_n = extend_node n "assign" in
    let fresh_edge = Assign (i, e) in
    let delta = fun s -> if s = fresh_n then [(fresh_edge, n)] else [] in
      (fresh_n, delta)
  | AST.Draw (i, e) ->
    let fresh_n = extend_node n "draw" in
    let fresh_edge = Draw (i, e) in
    let delta = fun s -> if s = fresh_n then [(fresh_edge, n)] else [] in
      (fresh_n, delta)
  | AST.ITE (b, l, r) ->
    let (ln, lg) = graph_of_ast l n in
    let (rn, rg) = graph_of_ast r n in
    let fresh_n = extend_node n "ite" in
    let true_edge = Assume b in
    let false_edge = Assume (AST.UnaryOp (Operation.Defaults.not_, b)) in
    let delta = (fun s ->
      let old_edges = (lg s) @ (rg s) in
      if s = fresh_n then [(true_edge, ln); (false_edge, rn)] @ old_edges else old_edges) in
        (fresh_n, delta)
  | AST.While (b, e) ->
    let fresh_n = extend_node n "while" in
    let (en, eg) = graph_of_ast e fresh_n in
    let loop_edge = Assume b in
    let exit_edge = Assume (AST.UnaryOp (Operation.Defaults.not_, b)) in
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
  let final_node = N (Name.of_string "finish") in
  let (init_node, delta) = graph_of_ast ast final_node in
  let states = Automata.Graph.reachable_states [init_node] delta in
    Automata.A (states, init_node, delta, [final_node])