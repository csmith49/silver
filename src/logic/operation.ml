module T = Types

type t = {
  name : Name.t;
  symbol : string;
  signature : Types.t;
}

(* to string is easy enough now, but of string requires a base set *)
let to_string : t -> string = fun o -> Name.to_string o.name

(* here we work to define the defaults *)
module Defaults = struct
  (* some default type constuctors *)
  let rational = T.Base T.Rational
  let boolean = T.Base T.Boolean
  let f xs o = T.Function (xs, o)

  (* TODO: this currently just contains type information - will need to add semantics and logical encoding *)

  (* unary ops *)
  let not_ = {
    name = Name.of_string "Not";
    symbol = "!";
    signature = f [boolean] boolean;
  }
  let negative = {
    name = Name.of_string "Negative";
    symbol = "-";
    signature = f [rational] rational;
  }
  let unary = [not_; negative]

  (* arithmetic *)
  let plus = {
    name = Name.of_string "Plus";
    symbol = "+";
    signature = f [rational ; rational] rational;
  }
  let mult = {
    name = Name.of_string "Mult";
    symbol = "*";
    signature = f [rational ; rational] rational;
  }
  let div = {
    name = Name.of_string "Div";
    symbol = "/";
    signature = f [rational ; rational] rational;
  }
  let minus = {
    name = Name.of_string "Minus";
    symbol = "-";
    signature = f [rational ; rational] rational;
  }
  let arithmetic = [plus; mult; div; minus]

  (* comparisons *)
  let eq = {
    name = Name.of_string "Eq";
    symbol = "==";
    signature = f [rational ; rational] boolean;
  }
  let neq = {
    name = Name.of_string "NEq";
    symbol = "!=";
    signature = f [rational ; rational] boolean;
  }
  let leq = {
    name = Name.of_string "LEq";
    symbol = "<=";
    signature = f [rational ; rational] boolean;
  }
  let geq = {
    name = Name.of_string "GEq";
    symbol = ">=";
    signature = f [rational ; rational] boolean;
  }
  let lt = {
    name = Name.of_string "LT";
    symbol = "<";
    signature = f [rational ; rational] boolean;
  }
  let gt = {
    name = Name.of_string "GT";
    symbol = ">";
    signature = f [rational ; rational] boolean;
  }
  let comparisons = [eq; neq; leq; geq; lt; gt]

  (* logical ops *)
  let and_ = {
    name = Name.of_string "And";
    symbol = "&";
    signature = f [boolean ; boolean] boolean;
  }
  let or_ = {
    name = Name.of_string "And";
    symbol = "|";
    signature = f [boolean ; boolean] boolean;
  }
  let logical = [and_; or_]

  (* distributions *)
  let lap = {
    name = Name.of_string "lap";
    symbol = "lap";
    signature = f [rational] rational;
  }
  let distributions = [lap]

  (* all the defined functions *)
  let defined = unary @ arithmetic @ comparisons @ logical @ distributions
end

(* and a method to find ones with matching names *)
let find_op (n : Name.t) : t option =
  CCList.find_opt (fun o -> o.name = n) Defaults.defined

let mk_op (f : Name.t) (n : int) : t = {
  name = f;
  symbol = Name.to_string f;
  signature = 
    let range = CCList.range 1 n in
    let mk_var = fun i -> Types.Variable (Name.extend f (string_of_int i)) in
      Types.Function (CCList.map mk_var range, mk_var 0);
  }