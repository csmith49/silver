(* despite the fact that we use rationals everywhere... *)
(* log isn't closed over Q - we have to switch to R for evaluating models *)
module Number = struct
  type t = CCFloat.t

  let format = CCFormat.float3

  let to_string : t -> string = string_of_float
end

type t =
  | Number of Number.t
  | Boolean of bool

exception Cast_error of string

let format f : t -> unit = function
  | Number n -> Number.format f n
  | Boolean b -> CCFormat.bool f b
(* minor alias for later *)
let format_value = format

let to_string : t -> string = function
  | Number n -> Number.to_string n
  | Boolean b -> if b then "true" else "false"

let to_num : t -> Number.t = fun x -> match x with
  | Number n -> n
  | _ -> raise (Cast_error ((to_string x) ^ " cannot be cast to num"))

let to_bool : t -> bool = fun x -> match x with
  | Boolean b -> b
  | _ -> raise (Cast_error ((to_string x) ^ " cannot be cast to bool"))

let of_num : Number.t -> t = fun n -> Number n

let of_rational : Rational.t -> t = fun q -> Number (Rational.to_float q)

let of_bool : bool -> t = fun n -> Boolean n


(* alias for the following modules *)
type t_alias = t

(* for representing uninterpreted functions and indexed variables *)
module FiniteMap = struct
  module ValueMap = CCMap.Make(struct type t = t_alias let compare = Pervasives.compare end)

  type t = t_alias ValueMap.t

  let get = ValueMap.get

  let of_list = ValueMap.of_list

  let rec format f : t -> unit = fun m ->
    CCFormat.fprintf f "{@[<hv 2>%a@]}" 
      (CCFormat.list ~sep:(CCFormat.return ",@;") format_entry) 
      (m |> ValueMap.to_list)
  and format_entry f = fun (k, v) ->
    CCFormat.fprintf f "@[%a@ =>@ %a@]" format_value k format_value v

  let to_string : t -> string = fun m -> m
    |> ValueMap.to_list
    |> CCList.map (fun (k, v) -> (to_string k) ^ " => " ^ (to_string v))
    |> CCString.concat ", "
    |> fun s -> "{" ^ s ^ "}"
end

(* a model just maps constants to values/finite maps *)
module Model = struct
  module NameMap = CCMap.Make(Name)

  exception Binding_error

  type entry =
    | Concrete of t_alias
    | Map of FiniteMap.t

  let format_entry f = function
    | Concrete v -> format_value f v
    | Map m -> FiniteMap.format f m

  let entry_to_string : entry -> string = function
    | Concrete v -> to_string v
    | Map m -> FiniteMap.to_string m

  let to_value : entry -> t_alias = function
    | Concrete x -> x
    | _ -> raise Binding_error

  let to_map : entry -> FiniteMap.t = function
    | Map m -> m
    | _ -> raise Binding_error

  type t = entry NameMap.t

  let get = NameMap.get

  let of_list = NameMap.of_list

  let rec format f = fun m ->
    CCFormat.fprintf f "@[<hv 1>{@;%a@;}@]"
      (CCFormat.list ~sep:(CCFormat.return ",@ ") format_entry') 
      (m |> NameMap.to_list)
  and format_entry' f = fun (k, v) ->
    CCFormat.fprintf f "@[<hv>@;%a => %a@]" Name.format k format_entry v

  let to_string : t -> string = fun m -> m
    |> NameMap.to_list
    |> CCList.map (fun (k, v) -> (Name.to_string k) ^ " => " ^ (entry_to_string v))
    |> CCString.concat ", "
    |> fun s -> "{" ^ s ^ "}"
end