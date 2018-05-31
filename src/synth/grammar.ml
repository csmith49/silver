module type KEY = sig
  type t
  val compare : t -> t -> int
end

module Make = functor (K : KEY) -> struct
  module KMap = CCMap.Make(K)

  type 'v production = {
    output : K.t;
    input : K.t list;
    apply : 'v list -> 'v;
  }

  type 'v state = ('v list) KMap.t

  type 'v t = ('v production) list

  (* constructing states *)
  let init : 'v state = KMap.empty

  let singleton : K.t -> 'v -> 'v state = fun k -> fun v -> KMap.singleton k [v]

  let merge_states (l : 'v state) (r : 'v state) : 'v state =
    KMap.merge (fun _ -> fun lv -> fun rv -> (CCOpt.map2 (@)) lv rv) l r

  (* getting from the state is a bit trickier, due to defaults *)
  let get : K.t -> 'v state -> 'v list = KMap.get_or ~default:[]

  let get_all : 'v state -> 'v list = fun s -> s
    |> KMap.to_list
    |> CCList.flat_map snd

  (* and applying a production to the state *)
  let apply : 'v production -> 'v state -> 'v list = fun p -> fun s -> p.input
    |> CCList.map (fun k -> get k s)
    |> CCList.cartesian_product
    |> CCList.map p.apply

  let add_pair : (K.t * 'v) -> 'v state -> 'v state = fun (k, v) -> fun s ->
    KMap.add k (v :: (get k s)) s

  (* and manipulating productions *)
  let constant_productions (g : 'v t) : 'v production list =
    CCList.filter (fun p -> CCList.is_empty p.input) g

  (* now generating constants and appending them to the state *)
  let constants : 'v t -> 'v state = fun g -> g
    |> constant_productions
    |> CCList.map (fun p -> (p.output, p.apply []))
    |> CCList.fold_left (fun s -> fun pair -> add_pair pair s) init

  (* generate one step more *)
  let derive (init : 'v state) : 'v t -> 'v state = fun g -> g
    |> CCList.flat_map (fun p -> 
      apply p init |> CCList.map (fun v -> 
        (p.output, v)))
    |> CCList.fold_left (fun s -> fun pair -> add_pair pair s) init

  (* now for making more *)
  let rec derive_upto (n : int) : 'v t -> 'v state = fun g -> match n with
    | 0 -> init
    | 1 -> constants g
    | n -> derive (derive_upto (n - 1) g) g
end