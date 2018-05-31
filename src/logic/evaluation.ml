exception Evaluation_error

(* for casting some basic expressions to values *)
let literal_to_value : AST.lit -> Value.t = function
  | AST.Rational q -> Value.of_rational q
  | AST.Boolean b -> Value.of_bool b

let rec evaluate (model : Value.Model.t) : AST.expr -> Value.t = function
  | AST.Literal l -> literal_to_value l
  | AST.Identifier i -> begin match i with
      | AST.Var n -> (Value.Model.get n model) |> CCOpt.get_exn |> Value.Model.to_value
      | AST.IndexedVar (n, i) ->
        let index = evaluate model i in
        let map = Value.Model.get n model |> CCOpt.get_exn |> Value.Model.to_map in
          Value.FiniteMap.get index map |> CCOpt.get_exn
    end
  | AST.BinaryOp (o, l, r) ->
    o.Operation.value_encoding [evaluate model l; evaluate model r]
  | AST.UnaryOp (o, e) ->
    o.Operation.value_encoding [evaluate model e]
  | AST.FunCall (f, args) ->
    f.Operation.value_encoding (CCList.map (evaluate model) args)