exception Evaluation_error of string

(* for casting some basic expressions to values *)
let literal_to_value : AST.lit -> Value.t = function
  | AST.Rational q -> Value.of_rational q
  | AST.Boolean b -> Value.of_bool b

let rec evaluate (model : Value.Model.t) : AST.expr -> Value.t = function
  | AST.Literal l -> literal_to_value l
  | AST.Identifier i -> begin match i with
      | AST.Var n ->  begin match Value.Model.get n model with
          | Some v -> Value.Model.to_value v
          | None -> raise (Evaluation_error ("No value for " ^ (Name.to_string n)))
        end
      | AST.IndexedVar (n, i) ->
        let index = evaluate model i in
        let map = Value.Model.get n model |> CCOpt.get_exn |> Value.Model.to_map in
          Value.FiniteMap.get index map |> CCOpt.get_exn
    end
  | AST.BinaryOp (o, l, r) ->
    o.Operation.value_encoding [evaluate model l; evaluate model r]
  | AST.UnaryOp (o, e) ->
    o.Operation.value_encoding [evaluate model e]
  (* the case for quantifiers *)
  | AST.FunCall (f, args) when CCList.mem Operation.equivalent f Operation.Defaults.quantifiers ->
    (* this needs to be fixed *)
    Value.Boolean false
  (* the case for any other function *)
  | AST.FunCall (f, args) ->
    f.Operation.value_encoding (CCList.map (evaluate model) args)

(* for encoding *)
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
      | _ -> raise (Encoding_error ("no type for " ^ (Name.to_string n)))
    end
  | AST.IndexedVar (n, e) -> begin match Types.Environment.get_type n c with
      | Some (Types.Indexed (dom, codom)) ->
        let f = S.F.mk (Name.to_string n) [type_to_sort dom] (type_to_sort codom) in
        let e' = encode c e in
          S.F.apply f [e']
      | _ -> raise (Encoding_error "indexed type not found")
    end
