(* encoding an expression as a z3 expr *)
let rec encode (e : Types.Environment.t) : AST.expr -> Solver.expr = function
  | AST.Literal l -> begin match l with
     | AST.Rational q -> encode_rational q
     | AST.Boolean b -> encode_boolean b
    end
  | AST.Identifier i -> encode_identifier e i
  | AST.BinaryOp (o, l, r) ->
    let l' = encode e l in
    let r' = encode e r in
      o.Operation.solver_encoding [l'; r']
  | AST.UnaryOp (o, b) ->
    let b' = encode e b in
      o.Operation.solver_encoding [b']
  | AST.FunCall (f, args) ->
    f.Operation.solver_encoding (CCList.map (encode e) args)
and encode_rational : Rational.t -> Solver.expr = function
  Rational.Q (n, d) -> Solver.Rational.mk_numeral_nd Solver.context n d
and encode_boolean : bool -> Solver.expr = fun b ->
  if b then Solver.Bool.mk_true Solver.context else Solver.Bool.mk_false Solver.context
and encode_identifier (e : Types.Environment.t) : AST.id -> Solver.expr = function
  | AST.Var n -> begin match Types.Environment.get_type n e with
      | Some a -> Solver.mk_const (Solver.name_to_symbol n) (Solver.type_to_sort a)
      | _ -> raise (Invalid_argument "can't convert a non-typed variable to a constant")
    end
  | AST.IndexedVar (n, i) -> begin match Types.Environment.get_type n e with
      | Some (Types.Indexed (dom, codom)) ->
        let i' = encode e i in
        let n' = Solver.Func.mk_func_decl Solver.context 
            (Solver.name_to_symbol n) 
            [Solver.type_to_sort dom] 
            (Solver.type_to_sort codom) 
        in
          Solver.Func.apply n' [i']
      | _ -> raise (Invalid_argument "can't find type for indexed variable")
    end

(* and evaluating an expression *)
let rec evaluate (m : Value.Model.t) : AST.expr -> Value.t = function
  | AST.Literal l -> begin match l with
      | AST.Rational q -> Value.Real (Rational.to_float q)
      | AST.Boolean b -> Value.Bool b
    end
  | AST.Identifier i -> begin match i with
      | AST.Var n -> Value.Model.value_to_base (Value.Model.get n m)
      | AST.IndexedVar (n, i) ->
        let i' = evaluate m i in
        let fm = Value.Model.value_to_map (Value.Model.get n m) in
          Value.of_float (Value.FiniteMap.get (Value.to_float i') fm)
    end
  | AST.BinaryOp (o, l, r) ->
    let l' = evaluate m l in
    let r' = evaluate m r in
      o.Operation.value_encoding [l'; r']
  | AST.UnaryOp (o, e) ->
    let e' = evaluate m e in
      o.Operation.value_encoding [e']
  | AST.FunCall (f, args) ->
    let args' = CCList.map (evaluate m) args in
      f.Operation.value_encoding args'