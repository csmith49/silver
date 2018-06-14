open Rational

(* the representation of functions *)
type op = Name.t

(* expressions represent the bulk of the structure we're interested in *)
type expr =
  | Literal of lit
  | Identifier of id
  | FunCall of op * expr list
and id =
  | Var of Name.t
  | IndexedVar of Name.t * expr
and lit =
  | Rational of Rational.t
  | Boolean of bool

(* annotations are pre/post conditions *)
type annotation = expr

(* the structure of a program as a whole - exprs are preserved, this will get converted to an automata *)
type t =
  | Assign of id * expr
  | Draw of id * expr
  | ITE of expr * t * t
  | While of expr * t
  | Block of t list

type quantifier =
  | Exists
  | ForAll

type program = annotation * t * annotation

let compare = Pervasives.compare
let eq = (=)

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
  | FunCall (f, es) -> 
    let f' = match Operation.find_op f with
      | Some op -> op.Operation.symbol
      | None -> Name.to_string f in
    begin match es with
      | [e] ->
        let e' = expr_to_string e in
          f' ^ "(" ^ e' ^ ")"
      | [l ; r] ->
        let l' = expr_to_string l in
        let r' = expr_to_string r in 
        l' ^ " " ^ f' ^ " " ^ r'
      | _ as args ->
        let args' = CCList.map expr_to_string args in
          f' ^ "(" ^ (CCString.concat ", " args') ^ ")"
    end

and quantifier_to_string : quantifier -> string = function
  | Exists -> "Exists"
  | ForAll -> "ForAll"

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

module Infix = struct
  let ( =. ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "Eq", [l ; r])

  let ( !. ) (e : expr) : expr =
    FunCall (Name.of_string "Not", [e])
  
  let ( &. ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "And", [l ; r])

  let ( |. ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "Or", [l ; r])

  let ( +. ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "Plus", [l ; r])

  let ( =>. ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "Implies", [l ; r])

  let ( <= ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "LEq", [l ; r])

  let ( >= ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "GEq", [l ; r])

  let ( > ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "GT", [l ; r])

  let var : string -> expr = fun s ->
    Identifier (Var (Name.of_string s))

  let var_i : (string * int) -> expr = fun (s, i) ->
    Identifier (Var (Name.set_counter (Name.of_string s) i))

  let int : int -> expr = fun i ->
    Literal (Rational (Rational.Q (i, 1)))

  let bool : bool -> expr = fun b ->
    Literal (Boolean b)
end