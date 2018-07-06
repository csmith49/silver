(* probability axioms parameterized by an uninterpreted function (really just a var for our use case) *)
type uif = AST.expr

(* we have a couple of special variables for describing patterns and whatnot *)
let f : AST.id = AST.Var (Name.of_string "f")
let x : AST.id = AST.Var (Name.of_string "x")

(* a concretized axiom has two components - semantics generation and cost generation *)
(* the idea is to generate a bunch of uif using synth and plug them in to get an encoding *)
type concretized_axiom = {
  semantics : uif -> AST.expr;
  cost : uif -> AST.expr;
}

(* to get concretized axioms, we need to have non-concrete ones *)
(* our goal is a function : concretize : expr -> expr -> axiom -> concretized_axiom *)
type axiom = {
  pattern : AST.expr; (* contains variables V disjoint from x, f *)
  abstract_semantics : AST.expr; (* in terms of x, f, V *)
  abstract_cost : AST.expr; (* in terms of f, V *)
}

(* the payoff *)
let concretize : AST.expr -> AST.expr -> axiom -> concretized_axiom option = fun id -> fun e -> fun a -> 
    let e_sub = Substitution.left_unify a.pattern e in
    match CCOpt.(>>=) e_sub (Substitution.add x id) with
      | Some s -> 
        let semantics_fun = fun uif -> 
          Substitution.apply a.abstract_semantics (Substitution.add f uif s |> CCOpt.get_exn) in
        let cost_fun = fun uif -> 
          Substitution.apply a.abstract_cost (Substitution.add f uif s |> CCOpt.get_exn) in
        Some {
          semantics = semantics_fun;
          cost = cost_fun;
        }
      | None -> None

(* some utility to make things cleaner *)
let mk (pat : string) (sem : string) (cost : string) = {
  pattern = Parse.parse_expr pat;
  abstract_semantics = Parse.parse_expr sem;
  abstract_cost = Parse.parse_expr cost;
}

(* and the defaults can go here *)
module Laplace = struct
  let var_1 = mk "lap(e)" "abs(x) <. (rat(1) /. e) *. log(rat(1) /. f)" "f"
  let var_2 = mk "lap(e) +. m" "abs(x -. m) <. (rat(1) /. e) *. log(rat(1) /. f)" "f"
  let var_3 = mk "m +. lap(e)" "abs(x -. m) <. (rat(1) /. e) *. log(rat(1) /. f)" "f"

  let all = [var_1; var_2; var_3]
end

module Bernoulli = struct
  let var_1 = mk "bern(p)" "x == true" "p"
  let var_2 = mk "bern(p)" "x == false" "rat(1) -. p"

  let all = [var_1; var_2]
end