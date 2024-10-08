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
  | Integer of Z.t
  | Rational of Q.t
  | Boolean of bool

(* annotations are pre/post conditions *)
type annotation = expr

(* and cost is the value of beta we care about - possibly symbolic *)
type cost = expr

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

type program = annotation * t * annotation * cost

let compare = Stdlib.compare
let eq = (=)

(* formatting and printing *)
let rec format f : expr -> unit = function
  | Literal l -> format_lit f l
  | Identifier id -> format_id f id
  | FunCall (op, args) ->
    let f' = match Operation.find_op op with
      | Some f -> f.Operation.symbol
      | None -> CCFormat.to_string Name.format op in
    match args with
      | [] -> CCFormat.fprintf f "%s" f'
      | [x] -> CCFormat.fprintf f "%s%a" f' format x
      | x :: y :: [] -> CCFormat.fprintf f "@[<1>(%a@ %s@ %a)@]" format x f' format y
      | rest -> CCFormat.fprintf f "@[%s(@[<1>%a@])@]" 
        f' 
        (CCFormat.list ~sep:(CCFormat.return ",@ ") format) rest
and format_lit f : lit -> unit = function
  | Integer i -> CCFormat.int f (Z.to_int i)
  | Rational q -> CCFormat.string f (Q.to_string q)
  | Boolean b -> CCFormat.bool f b
and format_id f : id -> unit = function
  | Var n -> Name.format f n
  | IndexedVar (n, i) ->
    CCFormat.fprintf f "%a[%a]" Name.format n format i

(* print statements *)

let rec lit_to_string : lit -> string = function
  | Integer i -> Z.to_string i
  | Rational q -> Q.to_string q
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
  let ( =@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "eq", [l ; r])

  let ( !@ ) (e : expr) : expr =
    FunCall (Name.of_string "not", [e])
  
  let ( &@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "and", [l ; r])

  let ( |@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "or", [l ; r])

  let ( +@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "plus", [l ; r])

  let ( +.@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "ratPlus", [l ; r])

  let ( =>@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "implies", [l ; r])

  let ( <=@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "leq", [l ; r])

  let ( <=.@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "ratLeq", [l ; r])

  let ( >=@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "geq", [l ; r])

  let ( >=.@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "ratGeq", [l ; r])

  let ( >@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "gt", [l ; r])

  let ( >.@ ) (l : expr) (r : expr) : expr =
    FunCall (Name.of_string "ratGt", [l ; r])
    

  (*  *)
  let var : string -> expr = fun s ->
    Identifier (Var (Name.of_string s))

  let var_i : (string * int) -> expr = fun (s, i) ->
    Identifier (Var (Name.set_counter (Name.of_string s) i))

  let rat : int -> expr = fun i ->
    Literal (Rational (Q.of_int i))

  let int : int -> expr = fun i ->
    Literal (Integer (Z.of_int i))

  let bool : bool -> expr = fun b ->
    Literal (Boolean b)
end