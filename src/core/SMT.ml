(* signature allowing us to avoid a global context right now *)
module type CONTEXT = sig
  val context : Z3.context
end

(* safe to open, contains only types and modules *)
module Make = functor (C : CONTEXT) -> struct
  
  module Sort = struct
    type t = Z3.Sort.sort
    let rational = Z3.Arithmetic.Real.mk_sort C.context
    let boolean = Z3.Boolean.mk_sort C.context
  end

  module Symbol = struct
    type t = Z3.Symbol.symbol
    let of_string : string -> t = Z3.Symbol.mk_string C.context
    let to_string : t -> string = Z3.Symbol.to_string
  end

  module Expr = struct
    type t = Z3.Expr.expr

    (* arithmetic *)
    let plus (l : t) (r : t) : t = Z3.Arithmetic.mk_add C.context [l; r]
    let mult (l : t) (r : t) : t = Z3.Arithmetic.mk_mul C.context [l; r]
    let div : t -> t -> t =  Z3.Arithmetic.mk_div C.context
    let minus (l : t) (r : t) = Z3.Arithmetic.mk_sub C.context [l; r]
    let negative : t -> t = Z3.Arithmetic.mk_unary_minus C.context

    (* boolean stuff *)
    let and_ (l : t) (r : t) : t = Z3.Boolean.mk_and C.context [l; r]
    let or_ (l : t) (r : t) : t = Z3.Boolean.mk_or C.context [l; r]
    let not : t -> t = Z3.Boolean.mk_not C.context

    (* comparisons *)
    let eq : t -> t -> t = Z3.Boolean.mk_eq C.context
    let neq (l : t) (r : t) : t = Z3.Boolean.mk_distinct C.context [l; r]
    let lt : t -> t -> t = Z3.Arithmetic.mk_lt C.context
    let gt : t -> t -> t = Z3.Arithmetic.mk_gt C.context
    let leq : t -> t -> t = Z3.Arithmetic.mk_le C.context
    let geq : t -> t -> t = Z3.Arithmetic.mk_ge C.context

    (* and constructing constants *)
    let bool : bool -> t = fun b -> 
      if b then Z3.Boolean.mk_true C.context else Z3.Boolean.mk_false C.context
    let rational : int -> int -> t =
      Z3.Arithmetic.Real.mk_numeral_nd C.context

    (* and variables *)
    let variable : string -> Sort.t -> t = Z3.Expr.mk_const_s C.context
  end

  module F = struct
    type t = Z3.FuncDecl.func_decl

    let mk : string -> Sort.t list -> Sort.t -> t = Z3.FuncDecl.mk_func_decl_s C.context
    let apply : t -> Expr.t list -> Expr.t = Z3.FuncDecl.apply

    let domain : t -> Sort.t list = Z3.FuncDecl.get_domain
    let codomain : t -> Sort.t = Z3.FuncDecl.get_range

    let symbol : t -> Symbol.t = Z3.FuncDecl.get_name
  end

  module Model = struct
    type t = Z3.Model.model
  end

  module Answer = struct
    type t =
      | Sat of Model.t
      | Unsat
      | Unknown
  end

  module Solver = struct
    type t = Z3.Solver.solver

    let make : unit -> t = fun _ -> Z3.Solver.mk_simple_solver C.context

    let add (solver : t) (e : Expr.t) = Z3.Solver.add solver [e]
    let assert_ (solver : t) (p : Expr.t) (e : Expr.t) = Z3.Solver.assert_and_track solver p e

    let check : t -> Expr.t list -> Answer.t = fun s -> fun es -> match Z3.Solver.check s es with
      | Z3.Solver.UNSATISFIABLE -> Answer.Unsat
      | Z3.Solver.UNKNOWN -> Answer.Unknown
      | Z3.Solver.SATISFIABLE -> Answer.Sat (CCOpt.get_exn @@ Z3.Solver.get_model s)
  end
end

module Default = Make(struct let context = Z3.mk_context [] end)

(* renaming modules to make things easier later *)
module Bool = Z3.Boolean
module Real = Z3.Arithmetic.Real
module Arith = Z3.Arithmetic
module Func = Z3.FuncDecl
module Model = Z3.Model

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
      | Types.Rational -> Real.mk_sort context
      | Types.Boolean -> Bool.mk_sort context
    end
  | _ -> raise (Invalid_argument "can't convert non-base types to sorts")

let name_to_symbol : Name.t -> Z3.Symbol.symbol =
  fun n -> Z3.Symbol.mk_string context (Name.to_string n)

let mk_const (symbol : Z3.Symbol.symbol) (s : Z3.Sort.sort) : expr = Z3.Expr.mk_const context symbol s

(* we want to be able to extract certain ocaml primitive values from expressions *)
module Extract = struct
  exception Extraction_error

  let to_bool : expr -> bool = fun e ->
    if Bool.is_true e then true 
    else if Bool.is_false e then false 
    else raise Extraction_error

  let to_rational : expr -> Rational.t = fun e ->
    let n = e |> Real.get_numerator |> Arith.Integer.get_int in
    let d = e |> Real.get_denominator |> Arith.Integer.get_int in
      Rational.Q (n, d)
end