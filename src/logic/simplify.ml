type template = Template of (AST.expr -> AST.expr option)

let mk (pattern : string) (result : string) : template =
  let patt = Parse.parse_expr pattern in
  let res = Parse.parse_expr result in
  Template (fun e -> match Substitution.left_unify patt e with
    | Some sub -> Some (Substitution.apply res sub)
    | None -> None)

let apply : template -> (AST.expr -> AST.expr option) = function
  Template t -> t

module Defaults = struct
  let not_idempotent = mk "!(!(x))" "x"

  let universal_to_existential = mk "!(forall(x, y))" "exists(x, !(y))"
  
  let distribute_not_and = mk "!(x & y)" "!x | !y"
  
  let distribute_not_or = mk "!(x | y)" "!x & ! y"

  let distribute_not_implication = mk "!(x => y)" "x & !y"

  (* these are the templates that will be applied *)
  (* we make no guarantee of confluence, termination, etc. *)
  (* but we assume the trs is normalizing below *)
  let all = [
    not_idempotent; 
    distribute_not_and;
    distribute_not_or;
    distribute_not_implication;
    universal_to_existential
  ]
end

(* we want to be able to tell if anything was changed, so we know when we *)
(* should start again from the top *)
type delta = {
  expression : AST.expr;
  changed : bool;
}

(* the simplest kind of simplification starts at the top *)
let root_simplify : AST.expr -> delta = fun e ->
  match Defaults.all |> CCList.filter_map (fun t -> apply t e) with
    | x :: _ -> {
      expression = x;
      changed = true;
    }
    | _ -> {
      expression = e;
      changed = false;
    }

(* working top-down, descend into term until an application is made *)
let rec simplify_td : AST.expr -> delta = fun e ->
  let e' = root_simplify e in
  if e'.changed then e' else match e'.expression with
    | AST.Identifier (AST.IndexedVar (n, i))->
      let i' = simplify_td i in {
        expression = AST.Identifier (AST.IndexedVar (n, i'.expression));
        changed = i'.changed;
      }
    | AST.FunCall (f, args) ->
      let args' = CCList.map simplify_td args in {
        expression = AST.FunCall (f, args' |> CCList.map (fun a -> a.expression));
        changed = CCList.exists (fun x -> x) (args' |> CCList.map (fun a -> a.changed));
      }
    | _ -> e'

(* simplification just repeatedly applies simplify_td until convergence *)
let rec simplify : AST.expr -> AST.expr = fun e ->
  let e' = simplify_td e in
  if e'.changed then simplify e'.expression else e'.expression