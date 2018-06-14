(* we'll be doing some ssa transformation as we go along *)
module SSA = struct
  type t = Types.Environment.t

  let increment : AST.id -> t -> t = fun id -> fun c -> match id with
    | AST.Var n -> Types.Environment.increment n c
    | AST.IndexedVar (n, _) -> Types.Environment.increment n c

  let update_id : AST.id -> t -> AST.id = fun id -> fun c -> match id with
    | AST.Var n -> AST.Var (Name.set_counter n (Types.Environment.get_counter n c))
    | AST.IndexedVar (n, e) -> AST.IndexedVar (Name.set_counter n (Types.Environment.get_counter n c), e)

  let rec update_expr : AST.expr -> t -> AST.expr = fun e -> fun c -> match e with
    | AST.Literal _ -> e
    | AST.Identifier i -> AST.Identifier (update_id i c)
    | AST.FunCall (f, args) -> AST.FunCall (f, CCList.map (fun e -> update_expr e c) args)
end

(* module aliases to simplify type expressions *)
module State = Program.State
module Label = Program.Label

(* another alias *)
type path = Program.path

(* steps annotate graph steps with type and index info *)
type step = {
  step : (State.t, Label.t) Graph.Path.step;
  variables : Types.Environment.t;
}

(* traces are thus effectively annotated paths *)
type t = step list

(* this might look weird, but we have to parameterize our search by a strat and it needs state *)
(* so instead it gives an answer and a new strategy to use *)
module Strategy = struct
  type t = S of (step -> (Probability.uif list * t))

  let apply : t -> (step -> (Probability.uif list * t)) = function S s -> s
end

(* for printing nicely *)
let path_to_string : path -> string = Graph.Path.to_string State.to_string Label.to_string

(* recursively from paths *)
let rec of_path (env : Types.Environment.t) : path -> t = function
  | [] -> []
  | edge :: rest ->
    let s, label, d = edge in
    let env, label = match label with
      | Label.Assign (i, e) ->
        let e' = SSA.update_expr e env in
        let env = SSA.increment i env in
        let i' = SSA.update_id i env in
        let label = Label.Assign (i', e') in
          (env, label)
      | Label.Assume e -> 
        let e' = SSA.update_expr e env in
        let label = Label.Assume e' in
          (env, label)
      | Label.Draw (i, e) ->
        let e' = SSA.update_expr e env in
        let env = SSA.increment i env in
        let i' = SSA.update_id i env in
        let label = Label.Draw (i', e') in
          (env, label) in
    let edge = (s, label, d) in
    let step = {
      step = edge;
      variables = env;
    } in
      step :: (of_path env rest)

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

  (* given a counter,  *)
  let extend (i : int) (env : Types.Environment.t) : Types.Environment.t =
    let rational = Types.Base Types.Rational in
    let boolean = Types.Base Types.Boolean in
    let local = [
      (Name.of_string "w", rational);
      (Name.of_string "h", boolean);
    ]
    in CCList.fold_left (fun e -> fun (n, t) ->
        Types.Environment.update n t e)
      env local
end

(* here's a big one - we need to convert to a formula capturing the semantics *)
(* there's a lot of ways to do this, so we have to parameterize by probability axioms and theories *)
type encoding = Constraint.t list

let encoding_to_string : encoding -> string = fun e -> e
  |> CCList.map (fun e -> e.Constraint.expression)
  |> CCList.map AST.expr_to_string
  |> CCString.concat " & "

open AST.Infix

(* we encode one step at a time, effectively incrementing the strategy as we do *)
let encode_step 
  (strat : Strategy.t) 
  (axioms : Probability.axiom list) 
  (i : int) : step -> Constraint.t list * Strategy.t = fun s -> 
    match s.step with (src, label, dest) -> match label with
      (* x = e & w = wp & h = hp *)
      | Label.Assign (x, e) -> 
        let _, strat = Strategy.apply strat s in
        let enc = 
          ((AST.Identifier x) =. e) &. 
          ((Vars.w i) =. (Vars.w (i - 1))) &. 
          ((Vars.h i) =. (Vars.h (i - 1))) |> Simplify.simplify in
        let env = Vars.extend i s.variables in
          ([Constraint.of_expr env enc], strat)
    (* (w = wp) & (h = (hp | !b)) *)
    | Label.Assume b -> 
      let _, strat = Strategy.apply strat s in
      let enc =
        ((Vars.w i) =. (Vars.w (i - 1))) &.
        (
          ((Vars.h i) =. ((Vars.h (i - 1)) |. (!. b)))
        ) |> Simplify.simplify in
      let env = Vars.extend i s.variables in
        ([Constraint.of_expr env enc], strat)
    | Label.Draw (x, e) ->
      (* s & w = wp + c & h = hp *)
      let f = fun (s, c) -> s &. 
        ((Vars.w i) =. ((Vars.w (i - 1) +. c))) &.
        ((Vars.h i) =. (Vars.h (i - 1))) |> Simplify.simplify in 
      let terms, strategy = Strategy.apply strat s in
      let to_pair c t = c.Probability.semantics t, c.Probability.cost t in
      let env = Vars.extend i s.variables in
      let interps = axioms
        |> CCList.filter_map (Probability.concretize (AST.Identifier x) e)
        |> CCList.flat_map (fun c -> CCList.map (fun t -> to_pair c t) terms)
        |> CCList.map f 
        |> CCList.map (Constraint.of_expr env) in
      (interps, strat)

(* and now we can encode the entire thing - note we don't quite need pre and post condition here too *)
let encode (env : Types.Environment.t) (strat : Strategy.t) (axioms : Probability.axiom list) : t -> encoding list =
  let rec aux ?(index=1) strat axioms = function
    | [] -> []
    | step :: rest -> let encodings, strat = encode_step strat axioms index step in
      encodings :: (aux ~index:(index + 1) strat axioms rest)
  in fun t -> t
    |> aux strat axioms
    |> CCList.cartesian_product

(* a default strategy *)
let rec vars_in_scope : Strategy.t = Strategy.S (
  fun s -> 
    let expr = match s.step with (src, lbl, dest) -> match lbl with
      | Label.Assign (_, e) -> e
      | Label.Assume b -> b
      | Label.Draw (_, e) -> e in
    let env = s.variables in
    let terms = expr
      |> Theory.extract_terms env
      |> Theory.G.get (Theory.symbol_from_type (Types.Base Types.Rational)|> CCOpt.get_exn) in
    (terms, vars_in_scope)
)