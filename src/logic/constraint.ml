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

let format f : t -> unit = fun c -> AST.format f c.expression

let to_string : t -> string = fun c -> AST.expr_to_string c.expression

let of_expr (m : Types.Environment.t) : AST.expr -> t = fun e -> {
  expression = e;
  encoding = Cata.encode m e;
}

(* for combining constraints *)
module Mk = struct
  let and_ (left : t) (right : t) : t = {
    expression = AST.Infix.(left.expression &. right.expression);
    encoding = S.Expr.and_ left.encoding right.encoding;
  }

  let or_ (left : t) (right : t) : t = {
    expression = AST.Infix.(left.expression |. right.expression);
    encoding = S.Expr.or_ left.encoding right.encoding;
  }

  (* constants *)
  let true_ : t = {
    expression = AST.Literal (AST.Boolean true);
    encoding = S.Expr.bool true;
  }
  let false_ : t = {
    expression = AST.Literal (AST.Boolean false);
    encoding = S.Expr.bool false;
  }
end

type conjunction = t list

let format_conjunction = CCFormat.list ~sep:(CCFormat.return "@ & @ ") format

let conjunction_to_string : conjunction -> string = fun conj -> conj
  |> CCList.map to_string
  |> CCString.concat ", "

module Answer = struct
  type t =
    | Sat of Value.Model.t
    | Unsat
    | Unknown
  
  let to_string : t -> string = function
    | Sat m -> "SAT: " ^ (Value.Model.to_string m)
    | Unsat -> "UNSAT"
    | Unknown -> "UNKNOWN"

  let is_unsat : t -> bool = function
    | Unsat -> true
    | _ -> false

  let format f : t -> unit = function
    | Sat m -> CCFormat.fprintf f "SAT:@; %a" Value.Model.format m
    | Unsat -> CCFormat.fprintf f "UNSAT"
    | Unknown -> CCFormat.fprintf f "UNKNOWN"
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

(* the payoff *)
let vprint (v : bool) (s : string) : unit = if v then print_endline s else ()

open CCFormat

(* well, actually this *)
let check_wrt_theory ?(verbose=false) (c : Types.Environment.t) : Theory.t -> conjunction -> Answer.t = 
  fun theory -> fun cs -> 
    let _ = if verbose then printf "@[<v>[THEORY/CHECKING]@; @[%a@]@;@]" format_conjunction cs else () in
    match check cs with
    (* we have to check if we know we know *)
    | Answer.Sat model ->
      (* if the model is consistent with an actual evaluation, it's really a model *)
      let _ = if verbose then printf 
        "@[<v>[THEORY/RESULT] Sat with model@; @[%a@]@;@]" Value.Model.format model else () in 
      let values = cs
        |> CCList.map (fun c -> c.expression)
        |> CCList.map (Cata.evaluate model) in
      if CCList.for_all (fun v -> v = (Value.of_bool true)) values then
        let _ = if verbose then printf "[THEORY] Model consistent with evaluation.@;" else () in
        Answer.Sat model
      (* if not, we need to add some more info about the functions in the theory *)
      else let axioms = cs
        |> CCList.map (fun c -> c.expression)
        |> CCList.flat_map (Theory.concretize c theory)
        |> CCList.map (of_expr c) in
      let num_axioms = CCList.length axioms in
      let failure_clause = cs
        |> CCList.map (fun c -> c.expression)
        |> CCList.filter (fun c -> (Cata.evaluate model c) = (Value.of_bool false))
        |> CCList.hd in
      let _ = if verbose then printf
        "@[<v>[THEORY/RESULT] Clause@ @[%a@]@ inconsistent with evaluation. Checking with %d axioms.@]@;" 
          AST.format failure_clause 
          num_axioms else () in
      let answer = check (cs @ axioms) in
      let _ = if verbose then printf 
        "[THEORY/RESULT] Result is %a@;" Answer.format answer else () in
      answer
    | _ as answer ->
      let _ = if verbose then printf
        "[THEORY] Result is %a@;" Answer.format answer else () in
      answer
