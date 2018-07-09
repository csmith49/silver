module Index = struct
  (* mapping names (from AST.Vars) to indices representing the effective "count" *)
  module NameMap = CCMap.Make(Name)
  type t = int NameMap.t

  (* not actually empty -- see get *)
  let initial : t = NameMap.empty

  (* getting and setting *)
  let get : Name.t -> t -> int = fun n -> NameMap.get_or ~default:0 (Name.reset_counter n)
  let set : Name.t -> int -> t -> t = NameMap.add

  (* incrementing just updates the name by one *)
  let increment : Name.t -> t -> t = fun n -> fun i ->
    let curr = get n i in
      set (Name.reset_counter n) (curr + 1) i

  (* merging takes element-wise max *)
  let merge : t -> t -> t = NameMap.union (fun k -> fun l -> fun r -> Some (max l r))

  (* updating an expression to refer to the current index per variable *)
  let rec update (e : AST.expr) (index : t) : AST.expr = match e with
    | AST.Literal _ -> e
    | AST.Identifier i -> let i' = match i with
        | AST.Var n -> AST.Var (Name.set_counter n (get n index))
        | AST.IndexedVar (n, i) -> AST.IndexedVar (n, update i index)
      in AST.Identifier i'
    | AST.FunCall (f, args) -> AST.FunCall (f, CCList.map (fun e -> update e index) args)

  (* reset all the counters *)
  let reset : AST.expr -> AST.expr = fun e -> update e initial
end

(* aliases, because we should be using them a lot *)
module State = Program.State
module Label = Program.Label

type path = (State.t, Label.t) Graph.Path.t
type step = (State.t, Label.t) Graph.Path.step

(* we'll encode each path as a sequence of assignments and assumptions *)
type cmd =
  | Assign of AST.expr * AST.expr
  | Assume of AST.expr

(* a trace is a sequence of commands *)
type t = cmd list

(* strategies may look weird, but we want to thread them through and maintain state *)
module Strategy = struct
  type uif = Probability.uif
  type environment = Types.Environment.t
  type t = S of (environment -> step -> (uif list * t))

  (* simple deconstructor *)
  let apply : t -> (environment -> step -> uif list * t) = function S s -> s
end

(* a default strategy *)
let rec vars_in_scope : Strategy.t = Strategy.S (
  fun env -> fun s -> 
    let expr = match s with (src, lbl, dest) -> match lbl with
      | Label.Assign (_, e) -> e
      | Label.Assume b -> b
      | Label.Draw (_, e) -> e
      | Label.Concrete c -> c.Label.semantics in
    let terms = expr
      |> Theory.extract_terms env
      |> Theory.G.get (Theory.symbol_from_type (Types.Base Types.Rational)|> CCOpt.get_exn) in
    (terms, vars_in_scope)
)

(* more direct strategy *)
let rec beta_strat : Strategy.t = Strategy.S (
  fun _ -> fun _ -> ([Parse.parse_expr "beta /. rat(n)"], beta_strat)
)

(* utility for weights and whatnot *)
module Variables = struct
  let w = AST.Identifier (AST.Var (Name.of_string "w"))
  let h = AST.Identifier (AST.Var (Name.of_string "h"))

  (* extend an environment to bind w and h *)
  let extend : Types.Environment.t -> Types.Environment.t = fun env ->
    let local = [
      (Name.of_string "w", Types.Base Types.Rational);
      (Name.of_string "h", Types.Base Types.Boolean);
    ] in
      CCList.fold_left (fun e -> fun (n, t) -> Types.Environment.update n t e) env local
end

(* axiomatization uses probability axioms and strategies to concretize a path *)
let rec axiomatize (env : Types.Environment.t)
  (strategy : Strategy.t) (axioms : Probability.axiom list) : path -> path list = function
    | [] -> []
    | trace ->
      let concretized, _ = CCList.fold_left (fun (axiomatized, strat) -> fun s ->
          let sl, strategy = axiomatize_step env strategy axioms s in
            (axiomatized @ [sl], strategy)
        )
        ([], strategy)
        trace in
      concretized |> CCList.cartesian_product
(* we handle one step at a time, threading the strategy as we go *)
and axiomatize_step (env : Types.Environment.t)
  (strategy : Strategy.t) (axioms : Probability.axiom list) : step -> step list * Strategy.t = fun s ->
    match s with (src, lbl, dest) -> match lbl with
      | Label.Draw (x, e) ->
        (* find possible terms to concretize uifs to *)
        let terms, strategy = Strategy.apply strategy env s in
        let concretized = axioms
          (* concretize all possible axioms *)
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
          |> CCList.map (fun c -> (src, c, dest)) in
        (* we return a non-concretized option as well *)
        (s :: concretized, strategy)
      | _ -> let _, strategy = Strategy.apply strategy env s in ([s], strategy)

(* encoding converts paths to words containing only assignments and assumptions *)
let encode_step : step -> cmd list = fun (src, lbl, dest) -> match lbl with
  (* x = e *)
  | Label.Assign (x, e) -> [
      Assign (AST.Identifier x, e);
    ]
  (* h = (h | !b) *)
  | Label.Assume b -> [
      Assign (Variables.h, AST.Infix.(Variables.h |@ (!@ b)));  
    ]
  (* true *)
  | Label.Draw _ -> []
  (* semantics & w = w + cost *)
  | Label.Concrete c -> [
      Assume (c.Label.semantics);
      Assign (Variables.w, AST.Infix.(Variables.w +.@ c.Label.cost));
  ]
let encode_simple_step : step -> cmd list = fun (src, lbl, dest) -> match lbl with
  (* x = e *)
  | Label.Assign (x, e) -> [
      Assign (AST.Identifier x, e);
    ]
  (* b *)
  | Label.Assume b -> [
      Assume b;
    ]
  (* true *)
  | Label.Draw _ -> []
  (* semantics & w = w + cost *)
  | Label.Concrete c -> [
      Assume (c.Label.semantics);
      Assign (Variables.w, AST.Infix.(Variables.w +.@ c.Label.cost))
    ]

(* lifting step encoding to whole path *)
let rec encode : path -> t = function
  | [] -> []
  | step :: rest ->
    (encode_step step) @ (encode rest)
let rec encode_simple : path -> t = function
  | [] -> []
  | step :: rest ->
    (encode_simple_step step) @ (encode_simple rest)

(* we can convert a trace to a constraint by threading an index and updating accordingly *)
let cmd_to_constraint (index : Index.t) : cmd -> Constraint.t * Index.t = function
  | Assign (x, e) ->
    let e' = Index.update e index in
    let index' = match x with
      | AST.Identifier (AST.Var n) -> Index.increment n index
      | _ -> index in
    let x' = Index.update x index' in
      AST.Infix.(x' =@ e'), index'
  | Assume b ->
    let b' = Index.update b index in
      b', index
let to_constraint (index : Index.t) : t -> Constraint.t * Index.t = fun path ->
  let rec aux path index = match path with
    | [] -> [], index
    | cmd :: rest -> 
      let x, intermediate_index = cmd_to_constraint index cmd in
      let xs, index' = aux rest intermediate_index in
        x :: xs, index' in
  let constraints, index = aux path index in
    (Constraint.conjunction constraints, index)

(* annotations provide mechanisms for converting pre and post conditions to cmd lists *)
module Annotation = struct
  (* pre & w = 0 & h = false *)
  let pre : AST.annotation -> cmd list = fun annot ->
    [
      Assume annot;
      Assign (Variables.w, AST.Infix.rat 0);
      Assign (Variables.h, AST.Infix.bool false);
    ]
  (* pre & w = 0 *)
  let simple_pre : AST.annotation -> cmd list = fun annot ->
    [
      Assume annot;
      Assign (Variables.w, AST.Infix.rat 0);
    ]
  (* w <= beta & (!h => post) *)
  (* negated, becomes w > beta | (!h & !post) *)
  let post (annot : AST.annotation) (beta : AST.cost) : cmd list =
    let cost = AST.Infix.(Variables.w >.@ beta) in
    let failure = AST.Infix.((!@ Variables.h) &@ (!@ annot)) in
    [
      Assume AST.Infix.(cost |@ failure);
    ]
  (* w <= beta & post *)
  (* negated, becomes w > beta | !post *)
  let simple_post (annot : AST.annotation) (beta : AST.cost) : cmd list =
    let cost = AST.Infix.(Variables.w >.@ beta) in
    let failure = AST.Infix.(!@ annot) in
    [
      Assume AST.Infix.(cost |@ failure);
    ]
end

(* if pre & path is feasible, we can use the simpler encoding *)
let is_simplifiable (env : Types.Environment.t) (pre : AST.annotation) : path -> bool = fun p ->
  let encoding = (Annotation.pre pre) @ (encode p) in
  let c, _ = to_constraint Index.initial encoding in
    Constraint.check env c |> Constraint.Answer.is_sat

let path_formula (env : Types.Environment.t)
  (pre : AST.annotation) (p : path) (post : AST.annotation) (cost : AST.cost) : Constraint.t =
    let encoding = if is_simplifiable env pre p then
        (Annotation.simple_pre pre)
          @ (encode_simple p)
          @ (Annotation.simple_post post cost)
      else
        (Annotation.pre pre)
          @ (encode p)
          @ (Annotation.post post cost) in
    let c, _ = to_constraint Index.initial encoding in
      c
