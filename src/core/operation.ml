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

(* comparisons can't be based on semantics *)
let to_tuple : t -> (Name.t * string * Types.t) = fun op ->
  (op.name, op.symbol, op.signature)

let compare (left : t) (right : t) : int =
  Pervasives.compare (to_tuple left) (to_tuple right)

let equivalent (left : t) (right : t) : bool =
  (compare left right) = 0

(* for building solver encodings and whatnot *)
exception Encoding_error of string

let lift_unary (f : 'a -> 'a) : 'a list -> 'a = function
  | [a] -> f a
  | _ -> raise (Encoding_error "failure in lift_unary")
let lift_binary (f : 'a -> 'a -> 'a) : 'a list -> 'a = function
  | [l; r] -> f l r
  | _ -> raise (Encoding_error "failure in lift_binary")

(* to string is easy enough now, but of string requires a default set of operators *)
let to_string : t -> string = fun o -> Name.to_string o.name

(* here we work to define the defaults *)
module Defaults = struct
  (* some default type constuctors *)
  let rational = T.Base T.Rational
  let boolean = T.Base T.Boolean
  let integer = T.Base T.Integer
  let alpha = T.Variable (Name.of_string "alpha")
  let f xs o = T.Function (xs, o)

  (* unary ops *)
  let not_ = {
    name = Name.of_string "not";
    symbol = "!";
    signature = f [boolean] boolean;
    value_encoding = lift_unary (Value.of_bool % not % Value.to_bool);
    solver_encoding = lift_unary S.Expr.not;
  }
  let negative = {
    name = Name.of_string "negative";
    symbol = "-";
    signature = f [integer] integer;
    value_encoding = lift_unary (Value.of_num % (fun f -> f *. -1.0) % Value.to_num);
    solver_encoding = lift_unary S.Expr.negative;
  }
  let rat_negative = {
    name = Name.of_string "ratNegative";
    symbol = "-.";
    signature = f [rational] rational;
    value_encoding = lift_unary (Value.of_num % (fun f -> f *. -1.0) % Value.to_num);
    solver_encoding = lift_unary S.Expr.negative;
  }
  let unary = [not_; negative; rat_negative]

  (* arithmetic *)
  let rat_plus = {
    name = Name.of_string "ratPlus";
    symbol = "+.";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w -> 
      Value.of_num ((Value.to_num v) +. (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.plus;
  }
  let rat_mult = {
    name = Name.of_string "ratMult";
    symbol = "*.";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num ((Value.to_num v) *. (Value.to_num w)));
    (* solver_encoding = lift_binary S.Expr.mult; *)
    solver_encoding =
      let uif = S.F.mk "mult" [S.Sort.rational ; S.Sort.rational] S.Sort.rational in
        fun xs -> S.F.apply uif xs;
  }
  let rat_div = {
    name = Name.of_string "ratDiv";
    symbol = "/.";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num ((Value.to_num v) /. (Value.to_num w)));
    (* solver_encoding = lift_binary S.Expr.div; *)
    solver_encoding =
      let uif = S.F.mk "div" [S.Sort.rational ; S.Sort.rational] S.Sort.rational in
        fun xs -> S.F.apply uif xs;
  }
  let rat_minus = {
    name = Name.of_string "ratMinus";
    symbol = "-.";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num ((Value.to_num v) -. (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.minus;
  }
  let abs = {
    name = Name.of_string "abs";
    symbol = "abs";
    signature = f [rational] rational;
    value_encoding = lift_unary (fun v -> v
      |> Value.to_num |> abs_float |> Value.of_num);
    solver_encoding = lift_unary (fun v -> 
      S.Expr.ite 
        (S.Expr.geq 
          v
          (S.Expr.rational 0 1)
        )
        v
        (S.Expr.negative v));
  }
  let max = {
    name = Name.of_string "max";
    symbol = "max";
    signature = f [rational ; rational] rational;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num (max (Value.to_num v) (Value.to_num w)));
    solver_encoding = lift_binary (fun v -> fun w ->
      S.Expr.ite
        (S.Expr.gt v w)
          v
          w
      );
  }
  let int_to_rat = {
    name = Name.of_string "rat";
    symbol = "rat:";
    signature = f [integer] rational;
    value_encoding = lift_unary (fun x -> x);
    solver_encoding = lift_unary S.Expr.int_to_rat;
  }
  let increment = {
    name = Name.of_string "inc";
    symbol = "inc";
    signature = f [integer] integer;
    value_encoding = lift_unary (fun v -> 
      Value.of_num ((Value.to_num v) +. 1.0));
    solver_encoding = lift_unary (fun v ->
      S.Expr.plus v (S.Expr.int 1));
  }
  let plus = {
    name = Name.of_string "plus";
    symbol = "+";
    signature = f [integer ; integer] integer;
    value_encoding = lift_binary (fun v -> fun w -> 
      Value.of_num ((Value.to_num v) +. (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.plus;
  }
  let mult = {
    name = Name.of_string "mult";
    symbol = "*";
    signature = f [integer ; integer] integer;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num ((Value.to_num v) *. (Value.to_num w)));
    (* solver_encoding = lift_binary S.Expr.mult; *)
    solver_encoding =
      let uif = S.F.mk "mult" [S.Sort.rational ; S.Sort.rational] S.Sort.rational in
        fun xs -> S.F.apply uif xs;
  }
  let div = {
    name = Name.of_string "div";
    symbol = "/";
    signature = f [integer ; integer] rational;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num ((Value.to_num v) /. (Value.to_num w)));
    (* solver_encoding = lift_binary S.Expr.div; *)
    solver_encoding =
      let uif = S.F.mk "div" [S.Sort.rational ; S.Sort.rational] S.Sort.rational in
        fun xs -> S.F.apply uif xs;
  }
  let minus = {
    name = Name.of_string "minus";
    symbol = "-";
    signature = f [integer ; integer] integer;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_num ((Value.to_num v) -. (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.minus;
  }
  let arithmetic = [plus; mult; div; minus; 
    rat_plus; rat_mult; rat_div; rat_minus; 
    abs; max; int_to_rat]

  (* comparisons *)
  let eq = {
    name = Name.of_string "eq";
    symbol = "==";
    signature = f [alpha ; alpha] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool (v = w));
    solver_encoding = lift_binary S.Expr.eq;
  }
  let neq = {
    name = Name.of_string "neq";
    symbol = "!=";
    signature = f [alpha ; alpha] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool (v !=  w));
    solver_encoding = lift_binary S.Expr.neq;
  }
  let leq = {
    name = Name.of_string "leq";
    symbol = "<=";
    signature = f [integer ; integer] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) <= (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.leq;
  }
  let geq = {
    name = Name.of_string "geq";
    symbol = ">=";
    signature = f [integer ; integer] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) >= (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.geq;
  }
  let lt = {
    name = Name.of_string "lt";
    symbol = "<";
    signature = f [integer ; integer] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) < (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.lt;
  }
  let gt = {
    name = Name.of_string "gt";
    symbol = ">";
    signature = f [integer ; integer] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) > (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.gt;
  }
  let rat_leq = {
    name = Name.of_string "ratLeq";
    symbol = "<=.";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) <= (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.leq;
  }
  let rat_geq = {
    name = Name.of_string "ratGeq";
    symbol = ">=.";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) >= (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.geq;
  }
  let rat_lt = {
    name = Name.of_string "ratLt";
    symbol = "<.";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) < (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.lt;
  }
  let rat_gt = {
    name = Name.of_string "ratGt";
    symbol = ">.";
    signature = f [rational ; rational] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_num v) > (Value.to_num w)));
    solver_encoding = lift_binary S.Expr.gt;
  }
  let comparisons = [eq; neq; 
    leq; geq; lt; gt;
    rat_leq; rat_geq; rat_lt; rat_gt]

  (* logical ops *)
  let and_ = {
    name = Name.of_string "and";
    symbol = "&";
    signature = f [boolean ; boolean] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_bool v) && (Value.to_bool w)));
    solver_encoding = lift_binary S.Expr.and_;
  }
  let or_ = {
    name = Name.of_string "or";
    symbol = "|";
    signature = f [boolean ; boolean] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      Value.of_bool ((Value.to_bool v) || (Value.to_bool w)));
    solver_encoding = lift_binary S.Expr.or_;
  }
  let implies = {
    name = Name.of_string "implies";
    symbol = "=>";
    signature = f [boolean; boolean] boolean;
    value_encoding = lift_binary (fun v -> fun w ->
      let v' = Value.to_bool v in
      let w' = Value.to_bool w in
      Value.of_bool (not v' || w'));
    solver_encoding = lift_binary S.Expr.implies;
  }
  let logical = [and_; or_; implies]

  let exists = {
    name = Name.of_string "exists";
    symbol = "exists";
    signature = f [integer; boolean] boolean;
    value_encoding = lift_unary (fun _ -> raise (Encoding_error "cannot yet evaluate existential"));
    solver_encoding = fun xs -> match xs with
      | [n; e] -> S.Quantifier.exists n e;
      | _ -> raise (Encoding_error "incorrect format for quantifier");
  }
  let forall = {
    name = Name.of_string "forall";
    symbol = "forall";
    signature = f [integer; integer; integer; boolean] boolean;
    value_encoding = (fun _ -> raise (Encoding_error "cannot evaluate universal"));
    solver_encoding = fun xs -> match xs with
      | [n; l; u; e] -> S.Quantifier.bounded_forall n l u e;
      | _ -> raise (Encoding_error "incorrect format for quantifier");
  }
  let quantifiers = [exists; forall]

  (* distributions *)
  let lap = {
    name = Name.of_string "lap";
    symbol = "lap";
    signature = f [rational] rational;
    value_encoding = lift_unary (fun x -> x);
    solver_encoding = 
      let uif = S.F.mk "lap" [S.Sort.rational] S.Sort.rational in
        fun xs -> S.F.apply uif xs;
  }
  let bern = {
    name = Name.of_string "bern";
    symbol = "bern";
    signature = f [rational] boolean;
    value_encoding = lift_unary (fun x -> Value.Boolean true);
    solver_encoding =
      let uif = S.F.mk "bern" [S.Sort.rational] S.Sort.boolean in
        fun xs -> S.F.apply uif xs;
  }
  let bb = {
    name = Name.of_string "bb";
    symbol = "bb";
    signature = f [rational] integer;
    value_encoding = lift_unary (fun x -> Value.Boolean true);
    solver_encoding =
      let uif = S.F.mk "bb" [S.Sort.rational] S.Sort.integer in
        fun xs -> S.F.apply uif xs;
  }
  let distributions = [lap; bern; bb]

  (* weird projections we need for bb *)
  let bbfst = {
    name = Name.of_string "bbfst";
    symbol = "bbfst";
    signature = f [integer] boolean;
    value_encoding = lift_unary (fun x -> Value.of_bool (x <= (Value.of_int 1)));
    solver_encoding = fun xs -> match xs with
      | [v] -> S.Expr.leq v (S.Expr.int 1)
      | _ -> raise (Encoding_error "incorrect arity for projection");
  }
  let bbsnd = {
    name = Name.of_string "bbsnd";
    symbol = "bbsnd";
    signature = f [integer] boolean;
    value_encoding = lift_unary (fun x -> Value.of_bool 
      (
        (x = (Value.of_int 1)) ||
        (x = (Value.of_int 3))
      ));
    solver_encoding = fun xs -> match xs with
      | [v] -> S.Expr.or_ (S.Expr.eq v (S.Expr.int 1)) (S.Expr.eq v (S.Expr.int 3))
      | _ -> raise (Encoding_error "incorrect arity for projection");
  }
  let projections = [bbfst ; bbsnd]

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
  let defined = 
    unary @ 
    arithmetic @ 
    comparisons @ 
    logical @ 
    distributions @ 
    complicated @ 
    quantifiers @
    projections
end

(* constructing simple ones on the fly *)
let mk_op (f : Name.t) (n : int) : t =
  let mk_var = fun i ->
    Types.Variable (Name.extend f (string_of_int i)) in
  let range = CCList.range 1 n in {
    name = f;
    symbol = Name.to_string f;
    signature = Types.Function (CCList.map mk_var range, mk_var 0);
    value_encoding = lift_unary (fun _ -> 
      raise (Encoding_error ("cannot evaluate unknown function: " ^ (Name.to_string f))));
    solver_encoding = fun xs -> 
    raise (Encoding_error ("cannot encode unknown function: " ^ (Name.to_string f)));
  }

(* and a method to find ones with matching names *)
let find_op (n : Name.t) : t option =
  CCList.find_opt (fun o -> o.name = n) Defaults.defined

(* check if a name corresponds to a quantifier *)
let is_quantifier : Name.t -> bool = 
  fun n -> CCList.mem (=) n (CCList.map (fun o -> o.name) Defaults.quantifiers)