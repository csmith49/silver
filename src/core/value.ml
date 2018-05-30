module FloatMap = CCMap.Make(struct type t = float let compare = Pervasives.compare end)

module FiniteMap = struct
  module FloatMap = CCMap.Make(struct type t = float let compare = Pervasives.compare end)

  exception Unbound_index of float

  type t = float FloatMap.t

  let get (f : float) (m : t) : float = match FloatMap.get f m with
    | Some f -> f
    | None -> raise (Unbound_index f)

  let to_string : t -> string = fun m ->
    let pp = fun (k, v) -> (string_of_float k) ^ " => " ^ (string_of_float v) in
    let vals = FloatMap.to_list m |> CCList.map pp |> CCString.concat ", " in
      "{" ^ vals ^ "}"

end

(* despite the fact that we use rationals everywhere else... *)
(* since they are not closed under log and exp, we switch to reals for evaluation *)
type t =
  | Real of float
  | Bool of bool

let to_string : t -> string = function
  | Real f -> string_of_float f
  | Bool b -> string_of_bool b
  
(* some helpers *)
let to_float : t -> float = function
  | Real f -> f
  | _ -> raise (Invalid_argument "can't extract a float from a bool")

let of_float : float -> t = fun f -> Real f

let to_bool : t -> bool = function
  | Bool b -> b
  | _ -> raise (Invalid_argument "can't extract a bool from a float")

let of_bool : bool -> t = fun b -> Bool b

(* alias for model *)
type t_alias = t

(* a model just maps constants to values/finite maps *)
module Model = struct
  module NameMap = CCMap.Make(Name)

  exception Binding_error

  type value = 
    | Base of t_alias
    | Indexed of FiniteMap.t

  type t = value NameMap.t

  let get (n : Name.t) (m : t) : value = match NameMap.get n m with
    | Some v -> v
    | None -> raise (Invalid_argument "value not bound!")

  (* casting to the types of values with failure *)
  let value_to_base : value -> t_alias = function
    | Base b -> b
    | _ -> raise Binding_error

  let value_to_map : value -> FiniteMap.t = function
    | Indexed m -> m
    | _ -> raise Binding_error
end