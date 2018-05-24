(* note 1 : axioms are parametrized by an uninterpreted function *)
(* from an implementation perspective, we'll leave this as an expression *)
type uif = AST.expr

(* note 2: axioms need to be able to do three things *)
(* -- 1: pattern match against a probabilistic asignment/expr *)
(* -- 2: generate the appropriate semantic expression *)
(* -- 3: generate the appropriate cost for enforcing the chosen semantics *)

(* to support pattern matching, we'll have substitutions and one-way unification *)
module Sub = struct
  module IdentMap = CCMap.Make(struct type t = AST.id let compare = Pervasives.compare end)

  type t = AST.expr IdentMap.t

  let empty : t = IdentMap.empty

  let singleton (k : AST.id) (v : AST.expr) : t = IdentMap.singleton k v

  let rec apply (e : AST.expr) (s : t) : AST.expr = match e with
    | AST.Literal _ -> e
    | AST.Identifier i -> IdentMap.get_or ~default:e i s
    | AST.BinaryOp (o, l, r) -> AST.BinaryOp (o, apply l s, apply r s)
    | AST.UnaryOp (o, e) -> AST.UnaryOp (o, apply e s)
    | AST.FunCall (f, args) -> AST.FunCall (f, CCList.map (fun e -> apply e s) args)

  let add (k : AST.id) (v : AST.expr) (s : t) : t option = match IdentMap.get k s with
    | Some v' -> if v = v' then Some s else None
    | None -> Some (IdentMap.add k v s)

  let merge (l : t) (r : t) : t option = 
    let f = (fun ss -> fun (k, v) -> 
        match ss with Some s -> add k v s | None -> None)
    in CCList.fold_left f (Some r) (IdentMap.to_list l)
  
  let merge_opt (l : t option) (r : t option) : t option = match l, r with
    | Some l, Some r -> merge l r
    | _ -> None

  let rec pmatch (pattern : AST.expr) (term : AST.expr) : t option = 
    if pattern = term then Some empty else match pattern, term with
      | AST.Identifier i, _ -> Some (singleton i term)
      | AST.BinaryOp (o, l, r), AST.BinaryOp (o', l', r') ->
        if o = o' then merge_opt (pmatch l l') (pmatch r r') else None
      | AST.UnaryOp (o, e), AST.UnaryOp (o', e') ->
        if o = o' then pmatch e e' else None
      | AST.FunCall (f, args), AST.FunCall (f', args') ->
        if f = f' then CCList.fold_left merge_opt (Some empty) (CCList.map2 pmatch args args') else None
      | _, _ -> None
end

type t = {
  pattern : AST.id * AST.expr;
  semantics : Sub.t -> uif -> AST.expr;
  cost : uif -> AST.expr;
}

(* we'll do points 2 and 3 simultaneously, starting with 2 *)
let pmatch (e : Program.Edge.t) (p : t) : Sub.t option = match e with
  | Program.Edge.Draw (i, e) -> begin match p.pattern with
    | (i', e') -> 
      Sub.merge_opt (Sub.pmatch (AST.Identifier i) (AST.Identifier i')) (Sub.pmatch e e')
    end
  | _ -> None

(* generate produces a function that takes f -> (phi, w) pairs *)
let generate (e : Program.Edge.t) (p : t) : (uif -> (AST.expr * AST.expr)) option =
  CCOpt.map (fun s -> fun f -> (p.semantics s f, p.cost f)) (pmatch e p)

(* now we can deal with some utility stuff *)
module Mk = struct
  (* we'll use the var "f" as a special placeholder for the uif *)
  let hole = AST.Var (Name.of_string "f")

  let p : string * string -> AST.id * AST.expr = fun (i, e) ->
    (Utility.parse_id i, Utility.parse_expr e)

  let s (e : string) : (Sub.t -> uif -> AST.expr) =
    let expr = Utility.parse_expr e in
      (fun s -> fun f ->
        Sub.apply (Sub.apply expr s) (Sub.singleton hole f)
      )
  
  let c (e : string) : uif -> AST.expr =
    let expr = Utility.parse_expr e in
      (fun f -> 
        Sub.apply expr (Sub.singleton hole f)
      )
end

let to_string : t -> string = fun ax ->
  let e' = match ax.pattern with (i, e) -> (AST.id_to_string i) ^ " ~ " ^ (AST.expr_to_string e) in
  let s' = AST.expr_to_string (ax.semantics (Sub.empty) (AST.Identifier Mk.hole)) in
  let c' = AST.expr_to_string (ax.cost (AST.Identifier Mk.hole)) in
    "Pr_{" ^ e' ^ "}[" ^ s' ^ "] <= " ^ c'

module Laplace = struct
  let var_1 = {
    pattern = Mk.p ("v", "lap(e)");
    semantics = Mk.s "abs(v) > (1 / e) * log(1 / f)";
    cost = Mk.c "f";
  }

  let var_2 = {
    pattern = Mk.p ("v", "lap(e) + m");
    semantics = Mk.s "abs(v - m) > (1 / e) * log(1 / f)";
    cost = Mk.c "f";
  }
end