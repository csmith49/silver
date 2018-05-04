open Name.Infix
open Rational

type expr =
  | Literal of lit
  | Identifier of id
  | BinaryOp of Operation.t * expr * expr
  | UnaryOp of Operation.t * expr
  | FunCall of id * expr list
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
    let o' = Operation.to_string o in
    let l' = expr_to_string l in
    let r' = expr_to_string r in
      "BinaryOp(" ^ o' ^ ", " ^ l' ^ ", " ^ r' ^ ")"
  | UnaryOp(o, e) ->
    let o' = Operation.to_string o in
    let e' = expr_to_string e in
      "UnaryOp(" ^ o' ^ ", " ^ e' ^ ")"
  | FunCall (f, es) ->
    let f' = id_to_string f in
    let es' = CCList.map expr_to_string es in
      "FunCall(" ^ f' ^ ", " ^ (CCString.concat ", " es') ^ ")"

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