open Core

exception Evaluation_error of string

(* for casting some basic expressions to values *)
let literal_to_value : AST.lit -> Value.t = function
  | AST.Rational q -> Value.of_rational q
  | AST.Boolean b -> Value.of_bool b
  | AST.Integer i -> Value.of_int i

let rec evaluate (model : Value.Model.t) : AST.expr -> Value.t = function
  | AST.Literal l -> literal_to_value l
  | AST.Identifier i -> begin match i with
      | AST.Var n ->  begin match Value.Model.get n model with
          | Some v -> Value.Model.to_value v
          | None -> raise (Evaluation_error ("No value for " ^ (Name.to_string n)))
        end
      | AST.IndexedVar (n, i) ->
        let index = evaluate model i in
        let map = Value.Model.get n model |> (CCOption.get_exn_or "") |> Value.Model.to_map in
          Value.FiniteMap.get [index] map |> (CCOption.get_exn_or "")
    end
  (* the case for quantifiers *)
  | AST.FunCall (f, _) when Operation.is_quantifier f ->
    (* this needs to be fixed *)
    Value.Boolean true
  (* the case for any other function *)
  | AST.FunCall (f, args) ->
    let op = match Operation.find_op f with
      | Some op -> op
      | None -> Operation.mk_op f (CCList.length args) in
    op.Operation.value_encoding (CCList.map (evaluate model) args)

(* for encoding *)
module S = SMT.Default

exception Encoding_error of string

let type_to_sort : Types.t -> S.Sort.t = function
  | Types.Base (Types.Rational) -> S.Sort.rational
  | Types.Base (Types.Boolean) -> S.Sort.boolean
  | Types.Base (Types.Integer) -> S.Sort.integer
  | _ -> raise (Encoding_error "not a base type")

let rec encode (c : Types.Environment.t) : AST.expr -> S.Expr.t = function
  | AST.Literal l -> encode_literal l
  | AST.Identifier i -> encode_identifier c i
  | AST.FunCall (f, args) ->
    let op = match Operation.find_op f with
      | Some op -> op
      | None -> Operation.mk_op f (CCList.length args) in
    op.Operation.solver_encoding (CCList.map (encode c) args)
and encode_literal : AST.lit -> S.Expr.t = function
  | AST.Rational q -> S.Expr.rational (Q.num q) (Q.den q)
  | AST.Boolean b -> S.Expr.bool b
  | AST.Integer i -> S.Expr.int i
and encode_identifier (c : Types.Environment.t) : AST.id -> S.Expr.t = function
  | AST.Var n -> begin match Types.Environment.get_type n c with
      | Some t -> S.Expr.variable (Name.to_string n) (type_to_sort t)
      | _ -> raise (Encoding_error ("no type for " ^ (Name.to_string n)))
    end
  | AST.IndexedVar (n, e) -> begin match Types.Environment.get_type n c with
      | Some (Types.Indexed (dom, codom)) ->
        let f = S.F.mk (Name.to_string n) [type_to_sort dom] (type_to_sort codom) in
        let e' = encode c e in
          S.F.apply f [e']
      | _ -> raise (Encoding_error "indexed type not found")
    end
