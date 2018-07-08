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

  let universal_to_existential = mk "!(forall(x, l, u, y))" "exists(x, ((x >= l) & (x <= u)) => !(y))"
  
  let distribute_not_and = mk "!(x & y)" "!x | !y"
  
  let distribute_not_or = mk "!(x | y)" "!x & ! y"

  let distribute_not_implication = mk "!(x => y)" "x & !y"

  let inverse_of_inverse = mk "rat(1) /. (x /. y)" "y /. x"
  let rat_inverse_of_inverse = mk "rat(1) /. (x /. y)" "(y /. x)"

  let additive_identity_one = mk "rat(0) +. x" "x"
  let additive_identity_two = mk "x +. rat(0)" "x"

  let multiplicative_identity_one = mk "rat(1) *. x" "x"
  let multiplicative_identity_two = mk "x *. rat(1)" "x"

  let drop_existential = mk "exists(x, y)" "y"

  let disjunctive_identity_one = mk "false | x" "x"

  let disjunctive_identity_two = mk "x | false" "x"

  let conjunctive_identity_one = mk "true & x" "x"

  let conjunctive_identity_two = mk "x & true" "x"

  (* these are the templates that will be applied *)
  (* we make no guarantee of confluence, termination, etc. *)
  (* but we assume the trs is normalizing below *)
  let all = [
    inverse_of_inverse;
    rat_inverse_of_inverse;
    not_idempotent; 
    distribute_not_and;
    distribute_not_or;
    distribute_not_implication;
    (* universal_to_existential; *)
    drop_existential;
    conjunctive_identity_one;
    conjunctive_identity_two;
    disjunctive_identity_one;
    disjunctive_identity_two;
    additive_identity_one;
    additive_identity_two;
    multiplicative_identity_one;
    multiplicative_identity_two;
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