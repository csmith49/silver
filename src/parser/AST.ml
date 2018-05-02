open Name.Infix
open Rational

type expr =
  | Literal of lit
  | Identifier of id
  | BinaryOp of Operation.t * expr * expr
  | UnaryOp of Operation.t * expr
  | FunCall of Operation.t * expr list
and id =
  | Var of Name.t
  | IndexedVar of Name.t * expr
and lit =
  | Rational of Rational.t
  | Boolean of bool

let rec lit_to_string : lit -> string = function
  | Rational q -> Rational.to_string q
  | Boolean b -> string_of_bool b
and id_to_string : id -> string = function
  | Var n -> Name.to_string n
  | IndexedVar (n, i) ->
    let n' = Name.to_string n in
    let i' = expr_to_string i in
      n' ^ "[" ^ i' ^ "]"
and expr_to_string : expr -> string = function
  | Literal l -> lit_to_string l
  | Identifier n -> id_to_string n
  | BinaryOp (o, l, r) ->
    let o' = Operation.to_string o in
    let l' = expr_to_string l in
    let r' = expr_to_string r in
      "BinaryOp(" ^ o' ^ ", " ^ l' ^ ", " ^ r' ^ ")"
  | UnaryOp(o, e) ->
    let o' = Operation.to_string o in
    let e' = expr_to_string e in
      "UnaryOp(" ^ o' ^ ", " ^ e' ^ ")"
  | FunCall (f, es) ->
    let f' = Operation.to_string f in
    let es' = CCList.map expr_to_string es in
      "FunCall(" ^ f' ^ ", " ^ (CCString.concat ", " es') ^ ")"