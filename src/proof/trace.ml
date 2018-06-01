module N = Program.Node
module E = Program.Edge

(* a trace is just a path through the program automata *)
type path = (N.t, E.t) Graph.Path.t

type step = {
  step : (N.t, E.t) Graph.Path.step;
  live_vars : Types.Environment.t;
}

type t = step list

(* this type might look weird, but we have to parameterize our search by a strategy and it needs state *)
(* so instead when you call it it gives you a bunch of possible subs and a new strategy to keep on using *)
type strategy = Strategy of (step -> (Probability.uif list * strategy))

(* for printing nicely *)
let path_to_string : path -> string = Program.path_to_string

(* we'll be doing some ssa transformation as we go along *)
module Counter = struct
  (* we're indexing names to see how many times they've been assigned to along the path *)
  module NameMap = CCMap.Make(Name)
  type t = int NameMap.t

  (* simple construction - not actually "empty", see get *)
  let init : t = NameMap.empty

  (* wrapper, to adjust verbage *)
  let clear_index : Name.t -> Name.t = Name.reset_counter

  (* get and increment *)
  let get : Name.t -> t -> int = fun n -> NameMap.get_or ~default:0 (clear_index n)

  let increment : Name.t -> t -> t = fun n -> fun c ->
    let current_value = get n c in NameMap.add (clear_index n) (current_value + 1) c

  let increment_by_id : AST.id -> t -> t = fun id -> fun c -> match id with
    | AST.Var n -> increment n c
    | AST.IndexedVar (n, _) -> increment n c

  (* we'll need to lift updating counters to the level of ids *)
  let update_id : AST.id -> t -> AST.id = fun id -> fun c -> match id with
    | AST.Var n -> AST.Var (Name.set_counter n (get n c))
    | AST.IndexedVar (n, i) -> AST.IndexedVar (Name.set_counter n (get n c), i)

  (* and then to expressions *)
  let rec update : AST.expr -> t -> AST.expr = fun e -> fun c -> match e with
    | AST.Literal _ -> e
    | AST.Identifier i -> AST.Identifier (update_id i c)
    | AST.BinaryOp (o, l, r) -> AST.BinaryOp (o, update l c, update r c)
    | AST.UnaryOp (o, e) -> AST.UnaryOp (o, update e c)
    | AST.FunCall (f, args) -> AST.FunCall (f, CCList.map (fun e -> update e c) args)

  (* and also environemnts *)
  let update_environment : Types.Environment.t -> t -> Types.Environment.t = fun e -> fun c -> e
    |> NameMap.to_list
    |> CCList.map (fun (n, t) -> (Name.set_counter n (get n c), t))
    |> Types.Environment.of_list
end

(* we'll build traces from paths *)
let rec of_path (env : Types.Environment.t) ?(counter=Counter.init) : path -> t = function
  | [] -> []
  | edge :: rest -> 
    let s, label, d = edge in 
    let counter, label = match label with
      | E.Assign (i, e) ->
        let counter = Counter.increment_by_id i counter in
        let label = E.Assign (Counter.update_id i counter, Counter.update e counter) in
          (counter, label)
      | E.Assume e -> (counter, label)
      | E.Draw (i, e) ->
        let counter = Counter.increment_by_id i counter in
        let label = E.Draw (Counter.update_id i counter, Counter.update e counter) in
          (counter, label) in
    let edge = (s, label, d) in
    let step = {
      step = edge;
      live_vars = Counter.update_environment env counter;
    } in
    step :: (of_path env ~counter:counter rest)