(* heirarchical names, but we're folding them up using hash functions *)
type t = {
  id : string;
  hash : int;
  counter : int;
}

(* simple constructors and printers *)
let of_string (s : string) : t = {
  id = s;
  hash = 0;
  counter = 0;
}
let to_string : t -> string = fun n ->
  let h = if n.hash = 0 then "" else ":" ^ (string_of_int n.hash) in
  let i = if n.counter = 0 then "" else ":" ^ (string_of_int n.counter) in
    (n.id) ^ i ^ h
  
(* comparison is done polymorphically - no natural order to induce anyways *)
let compare = Pervasives.compare

(* hashing *)
(* hashing ignores the counter *)
let hash : t -> int = fun n -> CCHash.poly (n.id, n.hash)

(* the thing that lets heirarchical names work *)
let extend (n : t) (s : string) : t = { n with
  id = s;
  hash = hash n;
}
let extend_by_int (n : t) (i : int) : t = extend n (string_of_int i)
let extend_by_name (l : t) (r : t) : t = { l with 
  hash = l.hash lxor (hash r)
}

(* as another axis where we can make things unique, we have counters/subscripts *)
let set_counter (n : t) : int -> t = fun c -> { n with counter = c }
let reset_counter (n : t) : t = { n with counter = 0 }

(* alternative syntax makes names slightly easier to work with - just import when relevant *)
module Infix = struct
  let ( <+ ) : t -> string -> t = extend
end