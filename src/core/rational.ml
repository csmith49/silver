(* type is super simple *)
type t = Q of int * int

let to_string : t -> string = function
  Q (n, d) -> (string_of_int n) ^ "/" ^ (string_of_int d)

(* simple operations work just as you'd expect *)
let add (l : t) (r : t) : t = match l, r with
  Q (a, b), Q (c, d) -> Q (a * d + c * b, b * d)