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

type t =
  | Assign of id * expr
  | Draw of id * expr
  | ITE of expr * t * t
  | While of expr * t
  | Block of t list

type quantifier =
  | Exists
  | ForAll
type domain =
  | Range of expr * expr
type annotation =
  | Simple of expr
  | Quantified of quantifier * Name.t * domain * expr 

type program = annotation * t * annotation

(* makes it easy to construct things elsewhere *)
module Mk = struct
  exception Empty_list

  let op (op : Operation.t) (xs : expr list) : expr = match xs with
    | e :: es ->  let f = fun l -> fun r -> BinaryOp (op, l, r) in
      CCList.fold_right f es e
    | [] -> raise Empty_list
end

(* utility functions *)

(* print statements *)

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
    let o' = o.Operation.symbol in
    let l' = expr_to_string l in
    let r' = expr_to_string r in
      l' ^ " " ^ o' ^ " " ^ r'
  | UnaryOp(o, e) ->
    let o' = o.Operation.symbol in
    let e' = expr_to_string e in
      o' ^ "(" ^ e' ^ ")"
  | FunCall (f, es) ->
    let f' = f.Operation.symbol in
    let es' = CCList.map expr_to_string es in
      f' ^ "(" ^ (CCString.concat ", " es') ^ ")"

let rec annotation_to_string : annotation -> string = function
  | Simple e -> "Simple(" ^ (expr_to_string e) ^ ")"
  | Quantified (q, i, d, e) ->
    let q' = quantifier_to_string q in
    let i' = Name.to_string i in
    let d' = domain_to_string d in
    let e' = expr_to_string e in
      "Quantified(" ^ q' ^ ", " ^ i' ^ ", " ^ d' ^ ", " ^ e' ^ ")"
and quantifier_to_string : quantifier -> string = function
  | Exists -> "Exists"
  | ForAll -> "ForAll"
and domain_to_string : domain -> string = function
  | Range (l, r) ->
    let l' = expr_to_string l in
    let r' = expr_to_string r in
      "Range(" ^ l' ^ ", " ^ r' ^ ")"

let rec to_string : t -> string = function
  | Assign (n, e) ->
    let n' = id_to_string n in
    let e' = expr_to_string e in
      "Assign(" ^ n' ^ ", " ^ e' ^ ")"
  | Draw (n, e) ->
    let n' = id_to_string n in
    let e' = expr_to_string e in
      "Draw(" ^ n' ^ ", " ^ e' ^ ")"
  | ITE (e, t, f) ->
    let e' = expr_to_string e in
    let t' = to_string t in
    let f' = to_string f in
      "ITE(" ^ e' ^ ", " ^ t' ^ ", " ^ f' ^ ")"
  | While (e, b) ->
    let e' = expr_to_string e in
    let b' = to_string b in
      "While(" ^ e' ^ ", " ^ b' ^ ")"
  | Block bs ->
    let bs' = CCList.map to_string bs in
      "Block(" ^ (CCString.concat ", " bs') ^ ")"