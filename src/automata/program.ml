(* the machinery necessary for representing program automata *)
open Name.Infix

(* edges maintain the operation performed while moving from state to state *)
module Label = struct
  type t =
    | Assume of AST.expr
    | Assign of AST.id * AST.expr
    | Draw of AST.id * AST.expr

  (* printing *)
  let format f = function
    | Assume e -> AST.format f e
    | Assign (i, e) ->
      CCFormat.fprintf f "@[%a = %a@]" AST.format_id i AST.format e
    | Draw (i, e) ->
      CCFormat.fprintf f "@[%a ~ %a@]" AST.format_id i AST.format e

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

  (* equality check *)
  let eq = (=)
end

(* tags are used to indicate where we might consider merging or adding back edges *)
module Tag = struct
  type t = Loop | Branch

  (* printing *)
  let to_string : t -> string = function
    | Loop -> "LOOP"
    | Branch -> "BRANCH"

  let format f = function
    | Loop -> CCFormat.fprintf f "LOOP"
    | Branch -> CCFormat.fprintf f "BRANCH"
end

(* nodes maintain a unique id - name.t, in this case - and a list of tags representing pertinent info *)
module State = struct
  type t = {
    id : Name.t;
    tags : Tag.t list;
  }
    
  (* printing *)
  let to_string : t -> string = fun n -> 
    let id = Name.to_string n.id in
    let tags = n.tags
      |> CCList.map Tag.to_string
      |> CCString.concat "/" in
    if tags = "" then id else id ^ "[" ^ tags ^ "]"

  let format f = fun n ->
    let tag_fmt = CCFormat.within "[" "]" (CCFormat.list ~sep:(CCFormat.return " /@ ") Tag.format) in
    if CCList.is_empty n.tags then CCFormat.fprintf f "%a" Name.format n.id else
      CCFormat.fprintf f "@[%a%a@]" Name.format n.id tag_fmt n.tags

  (* we make states unique when we can *)
  let counter = ref 0

  (* hierarchical names in action *)
  let extend (n : t) (s : string) : t =
    let i = !counter in
    let _ = counter := i + 1 in
    {
      id = n.id <+ (string_of_int i) <+ s;
      tags = [];
    }

  (* inverse printing *)
  let of_string : string -> t = fun s -> {
    id = Name.of_string s;
    tags = [];
  }

  (* add a tag to the list *)
  let set_tag : Tag.t -> t -> t = fun tag -> fun n -> {
    n with tags = tag :: n.tags;
  }

  (* comparisons to simplify stuff later *)
  let eq = (=)

  (* the canonical dump state *)
  let dump : t = {
    id = Name.of_string "dump";
    tags = [];
  }
end

(* our graph representation - critical for constructing the structure below *)
type graph = (State.t, Label.t) Graph.t
type path = (State.t, Label.t) Automata.concrete_path
type t = (State.t, Label.t) Automata.t

(* construction *)
let rec graph_of_ast (ast : AST.t) (n : State.t) : State.t * graph = match ast with
  | AST.Assign (i, e) ->
    let fresh_n = State.extend n "assign" in
    let fresh_edge = Label.Assign (i, e) in
    let delta = fun s -> if State.eq s fresh_n then [(fresh_edge, n)] else [] in
      (fresh_n, delta)
  | AST.Draw (i, e) ->
    let fresh_n = State.extend n "draw" in
    let fresh_edge = Label.Draw (i, e) in
    let delta : graph = fun s -> if State.eq s fresh_n then [(fresh_edge, n)] else [] in
      (fresh_n, delta)
  | AST.ITE (b, l, r) ->
    let (ln, lg) = graph_of_ast l n in
    let (rn, rg) = graph_of_ast r n in
    let fresh_n = State.extend n "ite" |> State.set_tag Tag.Branch in
    let true_edge = Label.Assume b in
    let false_edge = Label.Assume (AST.FunCall (Name.of_string "not", [b])) in
    let delta = (fun s ->
      let old_edges = (lg s) @ (rg s) in
      if State.eq s fresh_n then [(true_edge, ln); (false_edge, rn)] @ old_edges else old_edges) in
        (fresh_n, delta)
  | AST.While (b, e) ->
    let fresh_n = State.extend n "while" |> State.set_tag Tag.Loop in
    let (en, eg) = graph_of_ast e fresh_n in
    let loop_edge = Label.Assume b in
    let exit_edge = Label.Assume (AST.FunCall (Name.of_string "not", [b])) in
    let delta = (fun s ->
      let old_edges = eg s in
      if State.eq s fresh_n then [(loop_edge, en); (exit_edge, n)] @ old_edges else old_edges) in
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
  let final = State.of_string "finish" in
  let (start, delta) = graph_of_ast ast final in
  {
    Automata.states = 
      CCList.sort_uniq Pervasives.compare (Graph.reachable ~v_eq:State.eq [start] delta);
    start = start;
    delta = Graph.map_edge Automata.Symbol.lift delta;
    final = [final];
  }

(* printing *)
let to_string : t -> string = Automata.to_string State.to_string Label.to_string