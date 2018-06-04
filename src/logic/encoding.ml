module S = SMT.Default

exception Encoding_error of string

let type_to_sort : Types.t -> S.Sort.t = function
  | Types.Base (Types.Rational) -> S.Sort.rational
  | Types.Base (Types.Boolean) -> S.Sort.boolean
  | _ -> raise (Encoding_error "not a base type")

let rec encode (c : Types.Environment.t) : AST.expr -> S.Expr.t = function
  | AST.Literal l -> encode_literal l
  | AST.Identifier i -> encode_identifier c i
  | AST.BinaryOp (o, l, r) ->
    let l' = encode c l in
    let r' = encode c r in
      o.Operation.solver_encoding [l'; r']
  | AST.UnaryOp (o, e) ->
    o.Operation.solver_encoding [encode c e]
  | AST.FunCall (f, args) ->
    f.Operation.solver_encoding (CCList.map (encode c) args)
and encode_literal : AST.lit -> S.Expr.t = function
  | AST.Rational q -> begin match q with
      | Rational.Q (n, d) -> S.Expr.rational n d
    end
  | AST.Boolean b -> S.Expr.bool b
and encode_identifier (c : Types.Environment.t) : AST.id -> S.Expr.t = function
  | AST.Var n -> begin match Types.Environment.get_type n c with
      | Some t -> S.Expr.variable (Name.to_string n) (type_to_sort t)
      | _ -> raise (Encoding_error "type not found")
    end
  | AST.IndexedVar (n, e) -> begin match Types.Environment.get_type n c with
      | Some (Types.Indexed (dom, codom)) ->
        let f = S.F.mk (Name.to_string n) [type_to_sort dom] (type_to_sort codom) in
        let e' = encode c e in
          S.F.apply f [e']
      | _ -> raise (Encoding_error "indexed type not found")
    end


(* we also need to be able to encode pre and post conditions *)
open AST.Infix
let ast_of_int i = AST.Literal (AST.Rational (Rational.Q (i, 1)))

let encode_annotation (c : Types.Environment.t) : AST.annotation -> S.Expr.t = function
  | AST.Simple e -> encode c e
  | AST.Quantified (q, n, d, e) ->
    let n' = AST.Identifier (AST.Var n) in
    let lower, upper = match d with
      | AST.Range (l, u) -> l, u in
    match q with
      | AST.ForAll ->
        let expr = ((n' <= upper) &. (n' >= lower)) =>. e in
          encode c expr
      | AST.Exists ->
        let expr = !.(((n' <= upper) &. (n' >= lower)) =>. (!. e)) in
          encode c expr