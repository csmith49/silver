open Core

module Substitution = Substitution

(* just wrapping Name for now, but I reserve the right to change this *)
module Symbol = struct
  type t = Name.t

  let compare = Name.compare

  let format = Name.format

  let to_string : t -> string = Name.to_string

  let of_id : AST.id -> t = function
    | AST.Var n -> n
    | AST.IndexedVar (n, _) -> n

  let of_string : string -> t = Name.of_string

  let to_expr : t -> AST.expr = fun n ->
    AST.Identifier (AST.Var n)
end

(* concretize the grammar to use symbols as non-terminals *)
module SymbolGrammar = Grammar.Make(Symbol)

(* aliases, so I don't have to write SymbolGrammar all the time *)
type synthesizer = AST.expr SymbolGrammar.t

type pattern = AST.expr SymbolGrammar.production

type state = AST.expr SymbolGrammar.state

(* for printing patterns and whatnot *)
let pattern_to_string : pattern -> string = fun patt ->
  let dummy_inputs = CCList.map Symbol.to_expr patt.SymbolGrammar.input in
  let dummy_expr = patt.SymbolGrammar.apply dummy_inputs in
    AST.expr_to_string dummy_expr

let rec format_state f (state : state) =
  let entries = state
    |> SymbolGrammar.KMap.to_list in
  CCFormat.fprintf f "@[<v>%a@]@." (CCFormat.list ~sep:(CCFormat.return "@;") format_entry) entries
and format_entry f = fun (k, v) -> CCFormat.fprintf f "@;%a@ ->@ @[%a@]"
  Symbol.format k (CCFormat.list ~sep:(CCFormat.return ",@ ") AST.format) v

(* for easily making patterns *)
let update_id (prefix : Name.t) : AST.id -> AST.id = function
  | AST.Var n -> AST.Var (Name.extend_by_name n prefix)
  | AST.IndexedVar (n, i) -> AST.IndexedVar (Name.extend_by_name n prefix, i)

let rec extract_symbols ?(prefix=Name.of_string "") : 
  AST.expr -> AST.expr * (AST.id * Symbol.t) list = function
    | AST.Literal l -> (AST.Literal l, [])
    | AST.Identifier i -> 
      let i' = update_id prefix i in
      let s = Symbol.of_id i in
        (AST.Identifier i', [(i', s)])
    | AST.FunCall (f, args) ->
      let range = CCList.range 1 (CCList.length args) in
      let args', ss = args
        |> CCList.map2 (fun i -> fun a -> extract_symbols ~prefix:(Name.extend_by_int prefix i) a) range
        |> CCList.split
        |> CCPair.map_snd CCList.flatten
      in (AST.FunCall (f, args'), ss)

let pattern_of_pair : Symbol.t * AST.expr -> pattern = fun (s, e) ->
  let expr, ss = extract_symbols e in
  let vars, input = CCList.split ss in
  let app_fun = fun es -> Substitution.apply expr (Substitution.of_list (CCList.combine vars es)) in
  {
    SymbolGrammar.apply = app_fun;
    input = input;
    output = s;
  }

let mk : string * string -> pattern = fun (s, e) ->
  let s' = Parse.parse_id s in
  let e' = Parse.parse_expr e in
    pattern_of_pair (Symbol.of_id s', e')