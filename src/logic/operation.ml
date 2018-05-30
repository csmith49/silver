module T = Types

open CCFun

type t = {
  name : Name.t;
  symbol : string;
  signature : Types.t;
  value_encoding : Value.t list -> Value.t;
  solver_encoding : Solver.expr list -> Solver.expr;
}

(* for building solver encodings and whatnot *)
exception Encoding_error

let lift_unary (f : 'a -> 'a) : 'a list -> 'a = function
  | [a] -> f a
  | _ -> raise Encoding_error
let lift_binary (f : 'a -> 'a -> 'a) : 'a list -> 'a = function
  | [l; r] -> f l r
  | _ -> raise Encoding_error

(* to string is easy enough now, but of string requires a default set of operators *)
let to_string : t -> string = fun o -> Name.to_string o.name

(* for using operators and defining encodings easier *)
let (<*) (o : t) (f : Solver.expr list -> Solver.expr) : Solver.expr list -> Solver.expr =
  fun xs -> o.solver_encoding [f xs]

(* here we work to define the defaults *)
module Defaults = struct
  (* some default type constuctors *)
  let rational = T.Base T.Rational
  let boolean = T.Base T.Boolean
  let f xs o = T.Function (xs, o)

  (* unary ops *)
  let not_ = {
    name = Name.of_string "Not";
    symbol = "!";
    signature = f [boolean] boolean;
    value_encoding = lift_unary (Value.of_bool % not % Value.to_bool);
    solver_encoding = lift_unary (Solver.Bool.mk_not Solver.context);
  }
  let negative = {
    name = Name.of_string "Negative";
    symbol = "-";
    signature = f [rational] rational;
    value_encoding = lift_unary (Value.of_float % (fun f -> f *. -1.0) % Value.to_float);
    solver_encoding = lift_unary (Solver.Arith.mk_unary_minus Solver.context);
  }
  let unary = [not_; negative]

  (* arithmetic *)
  let plus = {
    name = Name.of_string "Plus";
    symbol = "+";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_float ((Value.to_float v) +. (Value.to_float w)));
    solver_encoding = Solver.Arith.mk_add Solver.context;
  }
  let mult = {
    name = Name.of_string "Mult";
    symbol = "*";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_float ((Value.to_float v) *. (Value.to_float w)));
    solver_encoding = Solver.Arith.mk_mul Solver.context;
  }
  let div = {
    name = Name.of_string "Div";
    symbol = "/";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_float ((Value.to_float v) /. (Value.to_float w)));
    solver_encoding = lift_binary (Solver.Arith.mk_div Solver.context);
  }
  let minus = {
    name = Name.of_string "Minus";
    symbol = "-";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_float ((Value.to_float v) -. (Value.to_float w)));
    solver_encoding = Solver.Arith.mk_sub Solver.context;
  }
  let arithmetic = [plus; mult; div; minus]

  (* comparisons *)
  let eq = {
    name = Name.of_string "Eq";
    symbol = "==";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_bool ((Value.to_float v) = (Value.to_float w)));
    solver_encoding = lift_binary (Solver.Bool.mk_eq Solver.context);
  }
  let neq = {
    name = Name.of_string "NEq";
    symbol = "!=";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_bool ((Value.to_float v) != (Value.to_float w)));
    solver_encoding = not_ <* eq.solver_encoding;
  }
  let leq = {
    name = Name.of_string "LEq";
    symbol = "<=";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_bool ((Value.to_float v) <= (Value.to_float w)));
    solver_encoding = lift_binary (Solver.Arith.mk_le Solver.context);
  }
  let geq = {
    name = Name.of_string "GEq";
    symbol = ">=";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_bool ((Value.to_float v) >= (Value.to_float w)));
    solver_encoding = lift_binary (Solver.Arith.mk_ge Solver.context);
  }
  let lt = {
    name = Name.of_string "LT";
    symbol = "<";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_bool ((Value.to_float v) < (Value.to_float w)));
    solver_encoding = lift_binary (Solver.Arith.mk_lt Solver.context);
  }
  let gt = {
    name = Name.of_string "GT";
    symbol = ">";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_bool ((Value.to_float v) > (Value.to_float w)));
    solver_encoding = lift_binary (Solver.Arith.mk_gt Solver.context);
  }
  let comparisons = [eq; neq; leq; geq; lt; gt]

  (* logical ops *)
  let and_ = {
    name = Name.of_string "And";
    symbol = "&";
    signature = f [boolean ; boolean] boolean;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_bool ((Value.to_bool v) && (Value.to_bool w)));
    solver_encoding = Solver.Bool.mk_and Solver.context;
  }
  let or_ = {
    name = Name.of_string "And";
    symbol = "|";
    signature = f [boolean ; boolean] boolean;
    value_encoding = lift_binary (fun v -> fun w -> Value.of_bool ((Value.to_bool v) || (Value.to_bool w)));
    solver_encoding = Solver.Bool.mk_or Solver.context;
  }
  let logical = [and_; or_]

  (* distributions *)
  let lap = {
    name = Name.of_string "lap";
    symbol = "lap";
    signature = f [rational] rational;
    value_encoding = lift_unary (fun x -> raise Encoding_error);
    solver_encoding = fun xs -> raise Encoding_error;
  }
  let distributions = [lap]

  (* all the defined functions *)
  let defined = unary @ arithmetic @ comparisons @ logical @ distributions
end

(* and a method to find ones with matching names *)
let find_op (n : Name.t) : t option =
  CCList.find_opt (fun o -> o.name = n) Defaults.defined

let mk_op (f : Name.t) (n : int) : t = 
  let mk_var = fun i -> Types.Variable (Name.extend f (string_of_int i)) in 
  let range = CCList.range 1 n in
  {
    name = f;
    symbol = Name.to_string f;
    signature = Types.Function (CCList.map mk_var range, mk_var 0);
    value_encoding = lift_unary (fun _ -> raise Encoding_error);
    solver_encoding = fun xs -> raise Encoding_error;
  }