open CCOption.Infix

(* very simply, we only have a few base types and indexed types *)
(* but for the full type inference, we need to reason about functions as well *)
(* note the lack of polymorphism - this makes things sooo much easier, and hopefully we don't need it *)
type t =
  | Base of base
  | Indexed of t * t
  | Function of (t list) * t
  | Variable of Name.t
and base =
  | Integer
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
  | Integer -> "N"
  | Rational -> "R"
  | Boolean -> "Bool"

let rec format f : t -> unit = function
  | Base b -> format_base f b
  | Indexed (d, c) ->
    CCFormat.fprintf f "@[%a => %a@]" format d format c
  | Variable v -> Name.format f v
  | Function (args, c) ->
    CCFormat.fprintf f "@[%a -> %a@]"
      (CCFormat.list ~sep:(CCFormat.return "*@ ") format) args
      format c
and format_base f : base -> unit = function
  | Integer -> CCFormat.fprintf f "N"
  | Rational -> CCFormat.fprintf f "R"
  | Boolean -> CCFormat.fprintf f "Bool"

let t_alias_to_string = to_string

(* simple enough subtyping *)
let rec subtypes (small : t) (large : t) : bool = 
  if small = large then true else match small, large with
    | Base s, Base l -> if s = l then true else begin match s, l with
      | Integer, Rational -> true (* here we specify that integers subtype rationals *)
      | _ -> false end
    | Indexed (d, c), Indexed (d', c') ->
      (subtypes c c') && (subtypes d' d)
    | Function (args, o), Function (args', o') ->
      (subtypes o o') && (CCList.for_all ((=) true) (CCList.map2 subtypes args' args))
    | _ -> false

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
  
  module Counter = struct
    type t = int NameMap.t

    (* not actually "empty" -- see get *)
    let init : t = NameMap.empty

    (* get and increment *)
    let get : Name.t -> t -> int = fun n -> NameMap.get_or ~default:0 (Name.reset_counter n)

    let set : Name.t -> int -> t -> t = NameMap.add
    
    let increment: Name.t -> t -> t = fun n -> fun c ->
      let curr = get n c in NameMap.add (Name.reset_counter n) (curr + 1) c
  
    let max : t -> t -> t = NameMap.union (fun _ -> fun l -> fun r -> Some (max l r))
  end

  type t = {
    types : t_alias NameMap.t;
    counters : Counter.t;
  }

  (* simplest trivial construction *)
  let empty : t = {
    types = NameMap.empty;
    counters = Counter.init;
  }

  (* simplest non-trivial construction *)
  let singleton (x : Name.t) (b : t_alias) : t = {
    types = NameMap.singleton x b;
    counters = Counter.init;
  }

  (* more complicated non-trivial construction *)
  let of_list : (Name.t * t_alias) list -> t = fun ls -> {
    types = NameMap.of_list ls;
    counters = Counter.init;
  }

  (* for checking constraints *)
  let get_type (x : Name.t) (env : t) : t_alias option =
    NameMap.get (Name.reset_counter x) env.types

  let get_counter (x : Name.t) (env : t) : int =
    Counter.get x env.counters

  (* picking out some useful things from counter *)
  let increment : Name.t -> t -> t = fun n -> fun env -> 
    {env with counters = Counter.increment n env.counters}
  
  (* get variables *)
  let variables : t -> Name.t list = fun env -> env.types
    |> NameMap.to_list
    |> CCList.map fst

  (* picking out the "live" variables *)
  let live_variables : t -> Name.t list = fun env -> env.types
    |> NameMap.to_list
    |> CCList.map fst
    |> CCList.map (fun x -> (x, Counter.get x env.counters))
    |> CCList.map (fun (x, i) -> Name.set_counter x i)

  (* for printing *)
  let to_string  (env : t) : string = 
    let env' = env
      |> live_variables
      |> CCList.map (fun x -> (x, get_type x env |> CCOption.get_exn_or ""))
      |> CCList.map (fun (k, v) -> (Name.to_string k) ^ " : " ^ (to_string v))
      |> CCString.concat ", "
    in "[" ^ env' ^ "]"

  let update (x : Name.t) (b : t_alias) (env : t) : t = 
    {env with types = NameMap.add x b env.types}

  let update_w_count (x : Name.t) (b : t_alias) (i : int) (env : t) : t =
    {
      types = NameMap.add x b env.types;
      counters = Counter.set x i env.counters;
    }

  let max (left : t) (right : t) : t = {
    left with counters = Counter.max left.counters right.counters;
  }
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
        CCOption.map Sub.simplify @@ Sub.merge_opt (unify l' r') (Some s)
    | None -> None
end