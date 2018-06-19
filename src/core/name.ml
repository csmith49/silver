(* heirarchical names, but we're folding them up using hash functions *)
type t = {
  id : string;
  hash : int;
  counter : int;
}

(* simple constructors and printers *)
let of_string (s : string) : t =
  try
    let s, ei = match CCString.Split.right ~by:"!" s with
      | Some (s, ei) -> s, "!" ^ ei
      | None -> s, "" in
    let rest, hash = match CCString.Split.right ~by:":" s with
      | Some (rest, hash') -> rest, (int_of_string hash')
      | None -> s, 0 in
    let id, counter = match CCString.Split.left ~by:"_" rest with
      | Some (id, counter') -> id, (int_of_string counter')
      | None -> rest, 0 in 
    {
      id = id ^ ei;
      hash = hash;
      counter = counter;
    }
  with _ -> raise (Invalid_argument (CCFormat.sprintf "cannot convert %s to name" s))

(* stringing *)
let to_string : t -> string = fun n ->
  let h = if n.hash = 0 then "" else ":" ^ (string_of_int n.hash) in
  let i = if n.counter = 0 then "" else "_" ^ (string_of_int n.counter) in
    (n.id) ^ i ^ h

(* formatting *)
let rec format f = fun n -> 
  CCFormat.fprintf f "%s%a%a" n.id format_counter n.counter format_hash n.hash
and format_counter f = fun c -> if c = 0 then CCFormat.fprintf f "" else
  CCFormat.fprintf f "_%d" c
and format_hash f = fun h -> if h = 0 then CCFormat.fprintf f "" else
  CCFormat.fprintf f ":%d" h

let to_tuple : t -> (string * int * int) = fun n ->
  (n.id, n.hash, n.counter)

(* comparison is done polymorphically - no natural order to induce anyways *)
let compare (left : t) (right : t) = Pervasives.compare (to_tuple left) (to_tuple right)

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
let counter (n : t) : int = n.counter

(* alternative syntax makes names slightly easier to work with - just import when relevant *)
module Infix = struct
  let ( <+ ) : t -> string -> t = extend
end