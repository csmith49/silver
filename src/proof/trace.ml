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

let apply : strategy -> (step -> (Probability.uif list * strategy)) = function
  Strategy s -> s

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

(* the next module is a utility tool for maintaining a list of the weight variables and flag vars *)
module Vars = struct
  let w (i : int) : AST.expr = 
    let n = Name.set_counter (Name.of_string "w") i in
      AST.Identifier (AST.Var n)
  
  let h (i : int) : AST.expr =
    let n = Name.set_counter (Name.of_string "h") i in
      AST.Identifier (AST.Var n)

  let get_name : AST.expr -> Name.t = function
    | AST.Identifier (AST.Var n) -> n
    | _ -> raise (Invalid_argument "not an appropriately generated name")

  let extend (i : int) (env : Types.Environment.t) : Types.Environment.t =
    let rational = Types.Base Types.Rational in
    let boolean = Types.Base Types.Boolean in
    let local = [
      (w i, rational);
      (w (i - 1), rational);
      (h i, boolean);
      (h (i - 1), boolean); ] in
    CCList.fold_left (fun e -> fun (v, t) -> 
        Types.Environment.update (get_name v) t e) 
      env local
end

(* here's a big one - we need to convert to a formula capturing the semantics *)
(* there's a lot of ways to do this, so we have to parameterize by probability axioms and theories *)
type encoding = AST.expr list

let encoding_to_string : encoding -> string = fun e -> e
  |> CCList.map AST.expr_to_string
  |> CCString.concat " & "

open AST.Infix

(* we encode one step at a time, effectively incrementing the strategy as we do *)
let encode_step 
  (strat : strategy) 
  (axioms : Probability.axiom list) 
  (i : int) : step -> AST.expr list * strategy = fun s -> 
    match s.step with (src, label, dest) -> match label with
      (* x = e & w = wp & h = hp *)
      | E.Assign (x, e) -> 
        let _, strat = apply strat s in
        let enc = 
          ((AST.Identifier x) =. e) &. 
          ((Vars.w i) =. (Vars.w (i - 1))) &. 
          ((Vars.h i) =. (Vars.h (i - 1))) in
        ([enc], strat)
    (* (w = wp) & ((h = hp) | !b) *)
    | E.Assume b -> 
      let _, strat = apply strat s in
      let enc =
        ((Vars.w i) =. (Vars.w (i - 1))) &.
        (
          ((Vars.h i) =. (Vars.h (i - 1))) |. (!. b)
        ) in
      ([enc], strat)
    | E.Draw (x, e) ->
      (* s & w = wp + c & h = hp *)
      let f = fun (s, c) -> s &. 
        ((Vars.w i) =. ((Vars.w (i - 1) +. c))) &.
        ((Vars.h i) =. (Vars.h (i - 1))) in 
      let terms, strategy = apply strat s in
      let to_pair c t = c.Probability.semantics t, c.Probability.cost t in
      let interps = axioms
        |> CCList.filter_map (Probability.concretize (AST.Identifier x) e)
        |> CCList.flat_map (fun c -> CCList.map (fun t -> to_pair c t) terms)
        |> CCList.map f in
      (interps, strat)


(* and now we can encode the entire thing - note we don't quite need pre and post condition here too *)
let encode (strat : strategy) (axioms : Probability.axiom list) : t -> encoding list =
  let rec aux ?(index=1) strat axioms = function
    | [] -> []
    | step :: rest -> let encodings, strat = encode_step strat axioms index step in
      encodings :: (aux ~index:(index + 1) strat axioms rest)
  in fun t -> CCList.cartesian_product (aux strat axioms t)

(* a default strategy *)
let rec vars_in_scope : strategy = Strategy (
  fun s -> 
    let expr = match s.step with (src, lbl, dest) -> match lbl with
      | E.Assign (_, e) -> e
      | E.Assume b -> b
      | E.Draw (_, e) -> e in
    let env = s.live_vars in
    let terms = expr
      |> Theory.extract_terms env
      |> Theory.G.get (Theory.symbol_from_type (Types.Base Types.Rational)|> CCOpt.get_exn) in
    (terms, vars_in_scope)
)