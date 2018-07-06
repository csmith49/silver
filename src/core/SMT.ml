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
    let integer = Z3.Arithmetic.Integer.mk_sort C.context
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

    let int_to_rat : t -> t = Z3.Arithmetic.Integer.mk_int2real C.context

    (* boolean stuff *)
    let and_ (l : t) (r : t) : t = Z3.Boolean.mk_and C.context [l; r]
    let or_ (l : t) (r : t) : t = Z3.Boolean.mk_or C.context [l; r]
    let not : t -> t = Z3.Boolean.mk_not C.context
    let implies (l : t) (r : t) : t = Z3.Boolean.mk_implies C.context l r
    let ite (c : t) (l : t) (r : t) : t = Z3.Boolean.mk_ite C.context c l r

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
    let int : int -> t =
      Z3.Arithmetic.Integer.mk_numeral_i C.context

    (* and variables *)
    let variable : string -> Sort.t -> t = Z3.Expr.mk_const_s C.context

    (* some type checking *)
    let is_bool : t -> bool = Z3.Boolean.is_bool
    let is_rational : t -> bool = Z3.Arithmetic.is_rat_numeral
    let is_int : t -> bool = Z3.Arithmetic.is_int

    (* and conversions *)
    let to_bool : t -> bool = fun e -> match Z3.Boolean.get_bool_value e with
      | Z3enums.L_FALSE -> false
      | Z3enums.L_TRUE -> true
      | _ -> raise (Invalid_argument "that's not a bool")

    let to_rational : t -> Rational.t = fun e -> Rational.of_ratio (Z3.Arithmetic.Real.get_ratio e)

    let to_int : t -> int = fun e -> Z3.Arithmetic.Integer.get_int e

    (* printing - no real format *)
    let to_string = Z3.Expr.to_string
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

    exception Model_error of string

    let constant_declarations : t -> F.t list = Z3.Model.get_const_decls
    let function_declarations : t -> F.t list = Z3.Model.get_func_decls

    let constants : t -> Symbol.t list = fun m -> m
      |> constant_declarations
      |> CCList.map F.symbol

    let functions : t -> Symbol.t list = fun m -> m
      |> function_declarations
      |> CCList.map F.symbol

    let get_constant : t -> Symbol.t -> Expr.t = fun m -> fun s ->
      let decl = constant_declarations m |> CCList.filter (fun d -> (F.symbol d) = s) |> CCList.hd in
      match Z3.Model.get_const_interp m decl with
        | Some result -> result
        | None -> raise (Model_error ("Constant symbol " ^ (Symbol.to_string s) ^ " not bound."))

    type entry = Expr.t list * Expr.t

    let get_function : t -> Symbol.t -> entry list = fun m -> fun s ->
      let decl = function_declarations m |> CCList.filter (fun d -> (F.symbol d) = s) |> CCList.hd in
      let interp = match Z3.Model.get_func_interp m decl with
        | Some result -> result
        | None -> raise (Model_error ("Function symbol " ^ (Symbol.to_string s) ^ " not bound.")) in
      let get_entry = 
        fun e -> (Z3.Model.FuncInterp.FuncEntry.get_args e, Z3.Model.FuncInterp.FuncEntry.get_value e) in
          CCList.map get_entry (Z3.Model.FuncInterp.get_entries interp)
  end

  module Answer = struct
    type t =
      | Sat of Model.t
      | Unsat
      | Unknown

    let is_unsat : t -> bool = function
      | Unsat -> true
      | _ -> false
  end

  module Solver = struct
    type t = Z3.Solver.solver

    exception Solver_error

    let make : unit -> t = fun _ -> Z3.Solver.mk_simple_solver C.context

    let add (solver : t) (e : Expr.t) = Z3.Solver.add solver [e]
    let assert_ (solver : t) (p : Expr.t) (e : Expr.t) = Z3.Solver.assert_and_track solver e p

    let propositional : string -> Expr.t = fun s -> Expr.variable s Sort.boolean

    let check : t -> Answer.t = fun s -> match Z3.Solver.check s [] with
      | Z3.Solver.UNSATISFIABLE -> Answer.Unsat
      | Z3.Solver.UNKNOWN -> Answer.Unknown
      | Z3.Solver.SATISFIABLE -> Answer.Sat (match Z3.Solver.get_model s with
          | Some model -> model
          | None -> raise Solver_error)
  end

  module Quantifier = struct
    let forall (x : Expr.t) (body : Expr.t) : Expr.t = 
      Z3.Quantifier.mk_forall_const 
        C.context 
        [x]
        body 
        None [] [] None None 
      |> Z3.Quantifier.expr_of_quantifier

    let bounded_forall (x : Expr.t) (lower : Expr.t) (upper : Expr.t) (body : Expr.t) : Expr.t =
      (* (Expr.and_ *)
        (* (Expr.and_ (Expr.is_int lower) (Expr.is_int upper))   *)
        (forall x (Expr.implies 
          (Expr.and_ (Expr.geq x lower) (Expr.lt x upper)) body))
      (* ) *)

    let exists (x : Expr.t) (body : Expr.t) : Expr.t =
      Z3.Quantifier.mk_exists_const
        C.context
        [x]
        body
        None [] [] None None
      |> Z3.Quantifier.expr_of_quantifier
  end
end

(* TODO : set context to generate total models only *)
module Default = Make(struct let context = Z3.mk_context [] end)