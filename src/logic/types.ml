open CCOpt.Infix

(* very simply, we only have a few base types and indexed types *)
(* but for the full type inference, we need to reason about functions as well *)
(* note the lack of polymorphism - this makes things sooo much easier, and hopefully we don't need it *)
type t =
  | Base of base
  | Indexed of t * t
  | Function of (t list) * t
  | Variable of Name.t
and base =
  | Rational
  | Boolean

(* an alias for later *)
type t_alias = t

(* simple helpers *)
let rec to_string : t -> string = function
  | Base b -> base_to_string b
  | Indexed (d, c) ->
    let d' = to_string d in
    let c' = to_string c in
      d'  ^ " => " ^ c'
  | Variable x -> "var:" ^ (Name.to_string x)
  | Function (args, o) ->
    let args' = CCString.concat " * " (CCList.map to_string args) in
    let o' = to_string o in
      args' ^ " -> " ^ o'
and base_to_string : base -> string = function
  | Rational -> "R"
  | Boolean -> "Bool"

let t_alias_to_string = to_string

module Sub = struct
  module NameMap = CCMap.Make(Name)

  type t = t_alias NameMap.t

  let identity : t = NameMap.empty

  let singleton (n : Name.t) (b : t_alias) = NameMap.singleton n b

  let add (n : Name.t) (b : t_alias) (s : t) : t option =
    match NameMap.get n s with
      | Some b' -> if b = b' then Some s else None
      | None -> Some (NameMap.add n b s)

  let get = NameMap.get

  let merge (l : t) (r : t) : t option =
    CCList.fold_left (fun a -> fun (k, v) -> a >>= (add k v)) (Some r) (NameMap.to_list l)

  let merge_opt (l : t option) (r : t option) : t option = match l, r with
    | Some l, Some r -> merge l r
    | _ -> None

  let rec apply (s : t) : t_alias -> t_alias = function
    | Base b -> Base b
    | Indexed (l, r) -> Indexed (apply s l, apply s r)
    | Function (xs, x) -> Function (CCList.map (apply s) xs, apply s x)
    | Variable n -> NameMap.get_or n ~default:(Variable n) s

  let simplify (s : t) : t =
    NameMap.map (apply s) s

  (* for printing *)
  let to_string  (env : t) : string = 
    let env' = env
      |> NameMap.to_list
      |> CCList.map (fun (k, v) -> (Name.to_string k) ^ " => " ^ (to_string v))
      |> CCString.concat ", "
    in "[" ^ env' ^ "]"
end

module Environment = struct
  module NameMap = CCMap.Make(Name)
  
  type t = t_alias NameMap.t

  (* simplest trivial construction *)
  let empty : t = NameMap.empty

  (* simplest non-trivial construction *)
  let singleton (x : Name.t) (b : t_alias) : t = NameMap.singleton x b

  (* more complicated non-trivial construction *)
  let of_list = NameMap.of_list

  (* for checking constraints *)
  let get_type (x : Name.t) (env : t) : t_alias option =
    NameMap.get x env

  (* for printing *)
  let to_string  (env : t) : string = 
    let env' = env
      |> NameMap.to_list
      |> CCList.map (fun (k, v) -> (Name.to_string k) ^ " : " ^ (to_string v))
      |> CCString.concat ", "
    in "[" ^ env' ^ "]"

  let update (x : Name.t) (b : t_alias) (env : t) : t = NameMap.add x b env
end

let rec unify (l : t) (r : t) : Sub.t option =
  if l = r then Some Sub.identity else match l, r with
    | _, Variable n -> Some (Sub.singleton n l)
    | Variable n, _ -> Some (Sub.singleton n r)
    | Indexed (a, b), Indexed (x, y) ->
      let d = unify a x in
      let c = unify b y in
        Sub.merge_opt d c
    | Function (xs, x), Function (ys, y) ->
      let ds = CCList.map2 unify xs ys in
      let c = unify x y in
        CCList.fold_left Sub.merge_opt c ds
    | _ -> None

module Constraint = struct
  type equation = E of t_alias * t_alias
  type t = equation list

  module Infix = struct
    let (<&>) (l : t) (r : t) : t = l @ r
    let (=:=) (l : t_alias) (r : t_alias) : t = [E (l, r)]
  end

  let top = []

  (* for printing *)
  let rec to_string (c : t) : string = 
    let c' = c
      |> CCList.map equation_to_string
      |> CCString.concat " & "
    in "{|" ^ c' ^ "|}"
  and equation_to_string : equation -> string = function
    | E (l, r) ->
      let l' = t_alias_to_string l in
      let r' = t_alias_to_string r in
        l' ^ " = " ^ r'

  (* our end goal - resolve a system using unification *)
  let rec resolve : t -> Sub.t option = function
  | [] -> Some Sub.identity
  | E (l, r) :: rest -> match resolve rest with
    | Some s ->
      (* let _ = print_endline (Sub.to_string s) in *)
      let l' = Sub.apply s l in
      let r' = Sub.apply s r in
        CCOpt.map Sub.simplify @@ Sub.merge_opt (unify l' r') (Some s)
    | None -> None
end