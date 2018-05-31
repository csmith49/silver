module T = Types
module S = SMT.Default

open CCFun

type t = {
  name : Name.t;
  symbol : string;
  signature : Types.t;
  value_encoding : Value.t list -> Value.t;
  solver_encoding : S.Expr.t list -> S.Expr.t;
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
    solver_encoding = lift_unary S.Expr.not;
  }
  let negative = {
    name = Name.of_string "Negative";
    symbol = "-";
    signature = f [rational] rational;
    value_encoding = lift_unary (Value.of_num % (fun f -> f *. -1.0) % Value.to_num);
    solver_encoding = lift_unary S.Expr.negative;
  }
  let unary = [not_; negative]

  (* arithmetic *)
  let plus = {
    name = Name.of_string "Plus";
    symbol = "+";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w -> 
      Value.of_num ((Value.to_num v) +. (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.plus;
  }
  let mult = {
    name = Name.of_string "Mult";
    symbol = "*";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num ((Value.to_num v) *. (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.mult;
  }
  let div = {
    name = Name.of_string "Div";
    symbol = "/";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num ((Value.to_num v) /. (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.div;
  }
  let minus = {
    name = Name.of_string "Minus";
    symbol = "-";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num ((Value.to_num v) -. (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.minus;
  }
  let arithmetic = [plus; mult; div; minus]

  (* comparisons *)
  let eq = {
    name = Name.of_string "Eq";
    symbol = "==";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) = (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.eq;
  }
  let neq = {
    name = Name.of_string "NEq";
    symbol = "!=";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) != (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.neq;
  }
  let leq = {
    name = Name.of_string "LEq";
    symbol = "<=";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) <= (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.leq;
  }
  let geq = {
    name = Name.of_string "GEq";
    symbol = ">=";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) >= (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.geq;
  }
  let lt = {
    name = Name.of_string "LT";
    symbol = "<";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) < (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.lt;
  }
  let gt = {
    name = Name.of_string "GT";
    symbol = ">";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) > (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.gt;
  }
  let comparisons = [eq; neq; leq; geq; lt; gt]

  (* logical ops *)
  let and_ = {
    name = Name.of_string "And";
    symbol = "&";
    signature = f [boolean ; boolean] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_bool v) && (Value.to_bool w)));
    solver_encoding = lift_binary S.Expr.and_;
  }
  let or_ = {
    name = Name.of_string "And";
    symbol = "|";
    signature = f [boolean ; boolean] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_bool v) || (Value.to_bool w)));
    solver_encoding = lift_binary S.Expr.or_;
  }
  let logical = [and_; or_]

  (* distributions *)
  let lap = {
    name = Name.of_string "lap";
    symbol = "lap";
    signature = f [rational] rational;
    value_encoding = lift_unary (fun x -> x);
    solver_encoding = fun xs -> raise Encoding_error;
  }
  let distributions = [lap]

  (* and the annoying ones we have to deal with *)
  let log = {
    name = Name.of_string "log";
    symbol = "log";
    signature = f [rational] rational;
    value_encoding = lift_unary (fun v -> Value.of_num (log (Value.to_num v)));
    solver_encoding =
      let uif = S.F.mk "log" [S.Sort.rational] S.Sort.rational in
        fun xs -> S.F.apply uif xs;
  }
  let complicated = [log]

  (* all the defined functions *)
  let defined = unary @ arithmetic @ comparisons @ logical @ distributions @ complicated
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