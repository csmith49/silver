module S = SMT.Default

(* these conversion functions are crucial *)
exception Conversion_error

let value_of_expr : S.Expr.t -> Value.t = fun e ->
  if S.Expr.is_bool e then Value.of_bool (S.Expr.to_bool e) else
  if S.Expr.is_rational e then Value.of_rational (S.Expr.to_rational e) else
    raise Conversion_error

let name_of_symbol : S.Symbol.t -> Name.t =
  fun s -> Name.of_string (S.Symbol.to_string s)

let fmap_of_entries : S.Model.entry list -> Value.FiniteMap.t = fun es -> es
  |> CCList.filter_map (fun (args, v) ->
      match args with [x] -> Some (value_of_expr x, value_of_expr v) | _ -> None)
  |> Value.FiniteMap.of_list
  
let convert_model : S.Model.t -> Value.Model.t = fun m ->
  let constants = S.Model.constants m
    |> CCList.map (fun c -> 
      (name_of_symbol c, Value.Model.Concrete (c |> S.Model.get_constant m |> value_of_expr))) in
  let indexed = S.Model.functions m
    |> CCList.map (fun c ->
      (name_of_symbol c, Value.Model.Map (c |> S.Model.get_function m |> fmap_of_entries))) in
    Value.Model.of_list (constants @ indexed)

(* a constraint just keeps a copy of the expression and encoding around *)
type t = {
  expression : AST.expr;
  encoding : S.Expr.t;
}

let of_expr (m : Types.Environment.t) : AST.expr -> t = fun e -> {
  expression = e;
  encoding = Encoding.encode m e;
}

type conjunction = t list

module Answer = struct
  type t =
    | Sat of Value.Model.t
    | Unsat
    | Unknown
  
  let to_string : t -> string = function
    | Sat m -> "SAT: " ^ (Value.Model.to_string m)
    | Unsat -> "UNSAT"
    | Unknown -> "UNKNOWN"
end

let check : conjunction -> Answer.t = fun cs ->
  let solver = S.Solver.make () in
  let prop_vars = cs
    |> CCList.length
    |> CCList.range 1
    |> CCList.map (fun i -> S.Solver.propositional ("p_" ^ (string_of_int i))) in
  let assertions = CCList.combine prop_vars (CCList.map (fun c -> c.encoding) cs) in
  let _ = CCList.iter (fun (p, e) -> S.Solver.assert_ solver p e) assertions in
  match S.Solver.check solver with
    | S.Answer.Sat m -> Answer.Sat (convert_model m)
    | S.Answer.Unsat -> Answer.Unsat
    | S.Answer.Unknown -> Answer.Unknown