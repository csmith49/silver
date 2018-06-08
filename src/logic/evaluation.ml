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