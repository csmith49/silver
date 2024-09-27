open Core
open Logic
open Automata

(* we'll be doing some ssa transformation as we go along *)
module SSA = struct
  type t = Types.Environment.t

  let increment : AST.id -> t -> t = fun id -> fun c -> match id with
    | AST.Var n -> Types.Environment.increment n c
    (* | AST.IndexedVar (n, _) -> Types.Environment.increment n c *)
    | AST.IndexedVar _ -> c

  let rec update_id : AST.id -> t -> AST.id = fun id -> fun c -> match id with
    | AST.Var n -> AST.Var (Name.set_counter n (Types.Environment.get_counter n c))
    (* | AST.IndexedVar (n, e)  -> AST.IndexedVar (Name.set_counter n (Types.Environment.get_counter n c), e) *)
    | AST.IndexedVar (n, e) -> AST.IndexedVar (n, update_expr e c)
  and update_expr : AST.expr -> t -> AST.expr = fun e -> fun c -> match e with
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

let format_step f s = CCFormat.fprintf f "%a" (Graph.Path.format_step State.format Label.format) s.step
let format_short_step f = CCFormat.fprintf f "%a" (Graph.Path.format_short_step State.format Label.format)

(* traces are thus effectively annotated paths *)
type t = step list

let format = CCFormat.list ~sep:(CCFormat.return "@;") format_step

(* this might look weird, but we have to parameterize our search by a strat and it needs state *)
(* so instead it gives an answer and a new strategy to use *)
module Strategy = struct
  type t = S of (step -> (Probability.uif list * t))

  let apply : t -> (step -> (Probability.uif list * t)) = function S s -> s
end

(* extracts the last environment in the trace *)
let environment : t -> Types.Environment.t option = fun trace -> trace 
  |> CCList.last_opt
  |> CCOption.map (fun s -> s.variables)

(* for printing nicely *)
let format_path = Graph.Path.format State.format Label.format

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
          (env, label) 
      | Label.Concrete c ->
        let e' = SSA.update_expr c.Label.expression env in
        let env = SSA.increment c.Label.variable env in
        let i' = SSA.update_id c.Label.variable env in
        let s' = SSA.update_expr c.Label.semantics env in
        let c' = SSA.update_expr c.Label.cost env in
        let label = Label.Concrete {
          Label.expression = e';
          variable = i';
          semantics = s';
          cost = c';
        } in (env, label) in
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
      (Name.of_string "w", rational, i);
      (Name.of_string "h", boolean, i);
    ]
    in CCList.fold_left (fun e -> fun (n, t, i) ->
        Types.Environment.update_w_count n t i e)
      env local
end

(* here's a big one - we need to convert to a formula capturing the semantics *)
(* there's a lot of ways to do this, so we have to parameterize by probability axioms and theories *)
type encoding = Constraint.t list

let format_encoding = CCFormat.list ~sep:(CCFormat.return "@ & @ ") Constraint.format

let encoding_to_string : encoding -> string = fun e -> e
  |> CCList.map (fun e -> e.Constraint.expression)
  |> CCList.map AST.expr_to_string
  |> CCString.concat " & "

(* axiomatizing converts some Draw steps to Concrete steps, incrementing strategy as we go *)
let axiomatize_step
  (strategy : Strategy.t) 
  (axioms : Probability.axiom list) : step -> step list * Strategy.t = fun s ->
    match s.step with (src, lbl, dest) -> match lbl with
      | Label.Draw (x, e) ->
        (* find possible terms to concretize uifs to *)
        let terms, strategy = Strategy.apply strategy s in
        let concretized = axioms
          (* concretize all axioms possible *)
          |> CCList.filter_map (Probability.concretize (AST.Identifier x) e)
          (* construct concrete labels *)
          |> CCList.flat_map (fun c -> 
            CCList.map (fun t -> Label.Concrete {
              Label.variable = x;
              expression = e;
              semantics = c.Probability.semantics t;
              cost = c.Probability.cost t;
            }) terms)
          (* replace label in s with concrete label from above *)
          |> CCList.map (fun c -> {s with step = (src, c, dest)}) in
        (* we return a non-concretized version of s in addition *)
        (s :: concretized, strategy)
      | _ -> let _, strategy = Strategy.apply strategy s in
        ([s], strategy)
  
(* now we can axiomatize an entire path by chaining the strategy along *)
let axiomatize (strategy : Strategy.t) (axioms : Probability.axiom list) : t -> t list = function
  | [] -> []
  | trace ->
    let concretized, _ =
      CCList.fold_left (fun (axiomatized, _strat) -> fun s -> 
        let sl, strategy = axiomatize_step strategy axioms s in
        axiomatized @ [sl], strategy) ([], strategy) trace in
    concretized |> CCList.cartesian_product

(* converting a step to a constraint is straightforward - enc_i *)
let step_to_constraint (i : int) : step -> Constraint.t = fun s ->
  let env = Vars.extend i s.variables in
  match s.step with (_src, lbl, _dest) -> let enc = match lbl with
    (* x = e & w = wp & h = hp *)
    | Label.Assign (x, e) ->
      let x = AST.Identifier x in
      AST.Infix.(
        (x =@ e) &@
        ((Vars.w i) =@ (Vars.w (i - 1))) &@
        ((Vars.h i) =@ (Vars.h (i - 1)))
      ) |> Simplify.simplify
    (* (w = wp) & (h = (hp | !b)) *)
    | Label.Assume b ->
      AST.Infix.(
        ((Vars.w i) =@ (Vars.w (i - 1))) &@
        (
          ((Vars.h i) =@ ((Vars.h (i - 1)) |@ (!@ b) ))
        )
      ) |> Simplify.simplify
    (* true & w = wp & h = hp *)
    | Label.Draw _ ->
      AST.Infix.(
        ((Vars.w i) =@ (Vars.w (i - 1))) &@
        ((Vars.h i) =@ (Vars.h (i - 1)))
      ) |> Simplify.simplify
    (* semantics & w = wp + cost & h = hp *)
    | Label.Concrete c ->
      let sem = c.Label.semantics in
      let cost = c.Label.cost in
      AST.Infix.(
        sem &@
        ((Vars.w i) =@ ((Vars.w (i - 1)) +.@ cost)) &@
        ((Vars.h i) =@ (Vars.h (i - 1)))
      ) |> Simplify.simplify
  in Constraint.of_expr env enc

(* a simpler encoding which eschews halt variables - only works if the trace is feasible *)
let simple_step_to_constraint (i : int) : step -> Constraint.t = fun s ->
  let env = Vars.extend i s.variables in
  match s.step with (_src, lbl, _dest) -> let enc = match lbl with
    (* x = e & w = wp *)
    | Label.Assign (x, e) ->
      let x = AST.Identifier x in
      AST.Infix.(
        (x =@ e) &@
        ((Vars.w i) =@ (Vars.w (i - 1)))
      ) |> Simplify.simplify
    (* w = wp & b *)
    | Label.Assume b ->
      AST.Infix.(
        ((Vars.w i) =@ (Vars.w (i - 1))) &@
        b
      ) |> Simplify.simplify
    (* w = wp *)
    | Label.Draw (_x, _e) ->
      AST.Infix.((Vars.w i) =@ (Vars.w (i - 1))) |> Simplify.simplify
    (* semantics & w = wp + cost *)
    | Label.Concrete c ->
      AST.Infix.(
      ((Vars.w i) =@ (Vars.w (i - 1)) +@ c.Label.cost) &@ c.Label.semantics) |> Simplify.simplify
    in Constraint.of_expr env enc

(* to convert a trace to a constraint, we just chain together the step_to_constraints and inc. i *)
let rec to_constraint ?(index=1) : t -> encoding = function
  | [] -> []
  | step :: rest ->
    let c = step_to_constraint index step in
    c :: (to_constraint ~index:(index + 1) rest)

let rec to_simple_constraint ?(index=1) : t -> encoding = function
  | [] -> []
  | step :: rest ->
    let c = simple_step_to_constraint index step in
    c :: (to_simple_constraint ~index:(index + 1) rest)

(* given a trace, strip the variable info and convert back to a path *)
let reset_step = fun s -> match s with (src, lbl, dest) -> 
  let reset_id i = SSA.update_id i Types.Environment.empty in
  let reset_expr e = SSA.update_expr e Types.Environment.empty in
  let lbl' = match lbl with
    | Label.Assign (i, e) ->
      Label.Assign (reset_id i, reset_expr e)
    | Label.Assume e -> Label.Assume (reset_expr e)
    | Label.Draw (i, e) ->
      Label.Draw (reset_id i, reset_expr e)
    | Label.Concrete c -> Label.Concrete 
      {
        Label.expression = reset_expr c.Label.expression;
        variable = reset_id c.Label.variable;
        semantics = reset_expr c.Label.semantics;
        cost = reset_expr c.Label.cost;
      }
  in (src, lbl', dest)

let to_path : t -> path = fun tr -> tr |> CCList.map (fun s -> s.step |> reset_step)

let to_word : t -> Label.t list = fun tr -> tr |> to_path |> Graph.Path.to_word

let format f t = CCFormat.fprintf f "%a" (Graph.Path.format State.format Label.format) (to_path t)

(* encoding a trace as a constraint - complex encoding if needed, otherwise simple encoding *)
module Encode = struct
  (* pre & w = 0 & h = false *)
  let pre (env : Types.Environment.t) : AST.annotation -> Constraint.t = fun annot ->
    let env = env |> Vars.extend 0 in
    let expr = AST.Infix.(annot &@ ((var "w") =@ (rat 0)) &@ ((var "h") =@ (bool false))) in
      Constraint.of_expr env expr
  
  (* pre & w = 0 *)
  let simple_pre (env : Types.Environment.t) : AST.annotation -> Constraint.t = fun annot ->
    let env = env |> Vars.extend 0 in
    let expr = AST.Infix.(annot &@ ((var "w") =@ (rat 0))) in
      Constraint.of_expr env expr

  (* !(w <= cost & (!h => post)) *)
  let post 
    (index : int) (env : Types.Environment.t) : AST.annotation -> AST.cost -> Constraint.t = fun annot -> fun c ->
      let env = env
        |> Vars.extend index
        |> Types.Environment.update (Name.of_string "betainternal") (Types.Base (Types.Rational)) in
      let c' = SSA.update_expr c env in
      let annot' = SSA.update_expr annot env in
      let expr = AST.Infix.(
        (!@ (((var_i ("w", index) <=@ c')) &@
        ((!@ (var_i ("h", index))) =>@ annot')))) in
      expr
        |> Simplify.simplify
        |> Constraint.of_expr env

  (* !(w <= cost & post) *)
  let simple_post
    (index : int) (env : Types.Environment.t) : AST.annotation -> AST.cost -> Constraint.t = fun annot -> fun c ->
      let env = env
        |> Vars.extend index
        |> Types.Environment.update (Name.of_string "betainternal") (Types.Base (Types.Rational)) in
      let c' = SSA.update_expr c env in
      let annot' = SSA.update_expr annot env in
      let expr = AST.Infix.(
        (!@ (((var_i ("w", index) <=@ c')) &@ annot'))) in
      expr
        |> Simplify.simplify
        |> Constraint.of_expr env
  
  let just_post (env : Types.Environment.t) : AST.annotation -> Constraint.t = fun annot ->
    let expr = AST.Infix.(
        (!@ (var "h")) =>@ annot
      ) in
    Constraint.of_expr env (SSA.update_expr expr env)

  let just_simple_post (env : Types.Environment.t) : AST.annotation -> Constraint.t = fun annot ->
    let expr = AST.Infix.(!@ annot) in
    Constraint.of_expr env (SSA.update_expr expr env)
end

(* check to see if we can use simpler encoding *)
let can_simplify ?(index=0) (env : Types.Environment.t) (pre : AST.annotation) (trace : t) : bool =
  let pre_encoding = Encode.pre env pre :: (to_constraint ~index:index trace) in
  match Constraint.check pre_encoding with
    | Constraint.Answer.Sat _ -> true
    | _ -> false

(* if we can get away with a simple encoding, do so, otherwise don't *)
let encode (_env : Types.Environment.t)
  (pre : AST.annotation) (trace : t) (post : AST.annotation) (cost : AST.cost) : Constraint.conjunction = 
    let pre_env = trace |> CCList.hd |> fun s -> s.variables in
    let post_env = trace |> CCList.last_opt |> CCOption.get_exn_or "" |> fun s -> s.variables in
    let length = CCList.length trace in
    if can_simplify pre_env pre trace then
      let pre = Encode.simple_pre pre_env pre in
      let post = Encode.simple_post length post_env post cost in
      let encoding = to_simple_constraint trace in
        pre :: (encoding @ [post])
    else
      let pre = Encode.pre pre_env pre in
      let post = Encode.post length post_env post cost in
      let encoding = to_constraint trace in
        pre :: (encoding @ [post])

(* a default strategy *)
let rec vars_in_scope : Strategy.t = Strategy.S (
  fun s -> 
    let expr = match s.step with (_src, lbl, _dest) -> match lbl with
      | Label.Assign (_, e) -> e
      | Label.Assume b -> b
      | Label.Draw (_, e) -> e
      | Label.Concrete c -> c.Label.semantics in
    let env = s.variables in
    let terms = expr
      |> Theory.extract_terms env
      |> Theory.G.get (Theory.symbol_from_type (Types.Base Types.Rational)|> CCOption.get_exn_or "") in
    (terms, vars_in_scope)
)

(* more direct strategy *)
let rec beta_strat : Strategy.t = Strategy.S (
  fun _ -> ([Parse.parse_expr "beta /. rat(n)"], beta_strat)
)
