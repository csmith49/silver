(* heirarchical names, but we're folding them up using hash functions *)
type t = Name of string * int

(* simple constructors and printers *)
let of_string (s : string) : t = Name (s, 0)
let to_string : t -> string = function Name (s, i) ->
  if i = 0 then s else s ^ ":" ^ (string_of_int i)

(* comparison is straightforward - by index, then by string *)
(* no clue if order actually matters *)
let compare (l : t) (r : t) : int = match l, r with
  Name (s, i), Name (t, j) ->
    let ans = CCInt.compare i j in match ans with
      | 0 -> CCString.compare s t
      | _ -> ans

(* hashing *)
(* several ways to to this, but the following has empirically been the most efficient *)
let hash : t -> int = CCHash.poly

(* the thing that lets heirarchical names work *)
let extend (n : t) (s : string) : t = Name (s, hash n)
let extend_by_name (l : t) (r : t) : t = match l, r with
  _, Name (t, j) -> Name (t, (hash l) lxor (CCInt.hash j))

(* alternative syntax makes names slightly easier to work with - just import when relevant *)
module Infix = struct
  let ( <+ ) : t -> string -> t = extend
  let ( ++ ) : t -> t -> t = extend_by_name
end