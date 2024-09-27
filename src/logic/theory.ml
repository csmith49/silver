open Core
open Synth

module SymbolMap = CCMap.Make(Synth.Symbol)
module NameMap = CCMap.Make(Name)

(* the start symbol, shared across all theories *)
let start : Synth.Symbol.t = Synth.Symbol.of_string "S"

(* the map from symbols to the types they represent *)
let types : Types.t SymbolMap.t = SymbolMap.of_list [
  (Synth.Symbol.of_string "rat", Types.Base Types.Rational);
  (Synth.Symbol.of_string "bool", Types.Base Types.Boolean);
]

(* we also have map from ids to symbols for the commonly used stuff *)
let symbols : Synth.Symbol.t NameMap.t = NameMap.of_list [
  (Name.of_string "x", Synth.Symbol.of_string "rat");
  (Name.of_string "y", Synth.Symbol.of_string "rat");
  (Name.of_string "z", Synth.Symbol.of_string "rat");
  (Name.of_string "a", Synth.Symbol.of_string "bool");
  (Name.of_string "b", Synth.Symbol.of_string "bool");
  (Name.of_string "c", Synth.Symbol.of_string "bool");
] 

(* well this just seems inefficient *)
let symbol_from_type : Types.t -> Synth.Symbol.t option = fun t -> types
  |> SymbolMap.to_list
  |> CCList.map CCPair.swap
  |> CCList.assoc_opt ~eq:(=) t

(* axioms are effectively just productions in the grammar *)
type axiom = Synth.pattern

(* and a theory is just a collection of axioms - conveniently, also a grammar *)
type t = axiom list

(* symbol extraction - we don't make each variable fresh here, unlike in synth/grammar *)
let rec extract_variables : AST.expr -> (AST.id * Synth.Symbol.t) list = function
  | AST.Literal _ -> []
  | AST.Identifier i -> begin match i with
      | AST.Var n -> [(i, NameMap.get n symbols |> CCOption.get_exn_or "")]
      | _ -> raise (Invalid_argument "Can't use indexed variables in these rules")
    end
  | AST.FunCall (_, args) ->
    CCList.uniq ~eq:(=) (CCList.flat_map extract_variables args)

(* we will easily make axioms from strings - just hijacking some functions from synth *)
let axiom_of_string : string -> axiom = fun s ->
  let e = Parse.parse_expr s in
  let ss = extract_variables e in
  let vars, input = CCList.split ss in
  let app_fun = fun es -> Substitution.apply e (Substitution.of_list (CCList.combine vars es)) in
  {
    Synth.SymbolGrammar.apply = app_fun;
    input = input;
    (* note that output is always start - we're not making deep terms here *)
    output = start;
  }

module G = Synth.SymbolGrammar

(* we want to be able to build up a set of constants from an expression *)
type state = AST.expr G.state

(* from an expression, we'll pick out all the terms with types that match the base types above *)
let rec extract_terms (c : Types.Environment.t) : AST.expr -> state = fun e ->
  let term = match Static.infer c e with
    | Some t -> begin match symbol_from_type t with
        | Some s -> G.singleton s e
        | None -> G.init
      end
    | None -> G.init in
  let children = match e with
    | AST.Identifier (AST.IndexedVar (_, i)) -> [i]
    | AST.FunCall (_, args) -> args
    | _ -> [] in
  let child_terms = CCList.map (extract_terms c) children in
    CCList.fold_left G.merge_states term child_terms

(* now, we can concretize a theorem over a term *)
let concretize (c : Types.Environment.t) : t -> AST.expr -> AST.expr list = fun theory -> fun e ->
  let terms = extract_terms c e in
  let derivations = G.derive terms theory in
    G.get start derivations

module Defaults = struct
  let log = [
    axiom_of_string "log(x) >. rat(0)";
    (* axiom_of_string "log(x /. y) == log(x) -. log(y)"; *)
    axiom_of_string "(x <=. rat(0)) => log(x) == rat(0)";
  ]

  let field = [
    (* axiom_of_string "(x *. y) == (y *. x)";
    axiom_of_string "(x *. (y *. z)) == ((x *. y) *. z)";
    axiom_of_string "(x *. (y +. z)) == ((x *. y) +. (x *. z))";
    axiom_of_string "((x +. y) *. z) == ((x *. z) + (y *. z))"; *)
    (* axiom_of_string "(x == rat(0)) => ((x *. y) == rat(0))" *)
  ]
  let all = log @ field
end