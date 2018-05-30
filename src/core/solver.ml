(* renaming modules to make things easier later *)
module Bool = Z3.Boolean
module Rational = Z3.Arithmetic.Real
module Arith = Z3.Arithmetic
module Func = Z3.FuncDecl

(* type wrappers to be used elsewhere *)
type solver = Z3.Solver.solver
type expr = Z3.Expr.expr

(* global contexts and whatnot *)
let context_args = []
let context : Z3.context = Z3.mk_context context_args

(* global solver, probably good enough *)
let solver = Z3.Solver.mk_simple_solver context

(* other utilities for converting to solver-specific things *)
let type_to_sort : Types.t -> Z3.Sort.sort = function
  | Types.Base a -> begin match a with
      | Types.Rational -> Rational.mk_sort context
      | Types.Boolean -> Bool.mk_sort context
    end
  | _ -> raise (Invalid_argument "can't convert non-base types to sorts")

let name_to_symbol : Name.t -> Z3.Symbol.symbol =
  fun n -> Z3.Symbol.mk_string context (Name.to_string n)

let mk_const (symbol : Z3.Symbol.symbol) (s : Z3.Sort.sort) : expr = Z3.Expr.mk_const context symbol s