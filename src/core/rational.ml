(* type is super simple *)
type t = Q of int * int

(* printing *)
let to_string : t -> string = function
  Q (n, d) -> (string_of_int n) ^ "/" ^ (string_of_int d)

(* formatting *)
let format f = function
  Q (n, d) -> if d = 1 
    then CCFormat.int f n
    else CCFormat.fprintf f "%i / %i" n d

(* casting to float *)
let to_float : t -> float = function
  Q (n, d) -> (float_of_int n) /. (float_of_int d)

let of_ratio : Ratio.ratio -> t = fun r ->
  let n = Big_int.int_of_big_int (Ratio.numerator_ratio r) in
  let d = Big_int.int_of_big_int (Ratio.denominator_ratio r) in
    Q (n, d)

(* simple operations work just as you'd expect *)
let add (l : t) (r : t) : t = match l, r with
  Q (a, b), Q (c, d) -> Q (a * d + c * b, b * d)