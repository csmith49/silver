type template = Template of (AST.expr -> AST.expr option)

let mk (pattern : string) (result : string) : template =
  let patt = Utility.parse_expr pattern in
  let res = Utility.parse_expr result in
  Template (fun e -> match Substitution.left_unify patt e with
    | Some sub -> Some (Substitution.apply res sub)
    | None -> None)

let apply : template -> (AST.expr -> AST.expr option) = function
  Template t -> t

module Defaults = struct
  let not_idempotent = mk "!(!(x))" "x"

  (* these are the templates that will be applied *)
  (* we make no asssumption of confluence, termination, etc. *)
  let all = [not_idempotent]
end

(* just apply in some order *)
let rec simplify_children : AST.expr -> AST.expr = function
  | AST.Identifier (AST.IndexedVar (n, e)) ->
    AST.Identifier (AST.IndexedVar (n, simplify e))
  | AST.BinaryOp (o, l, r) ->
    AST.BinaryOp (o, simplify l, simplify r)
  | AST.UnaryOp (o, e) ->
    AST.UnaryOp (o, simplify e)
  | AST.FunCall (f, args) ->
    AST.FunCall (f, CCList.map simplify args)
  | _ as e -> e
and simplify : AST.expr -> AST.expr = fun e ->
  let e' = simplify_children e in
  match Defaults.all |> CCList.filter_map (fun t -> apply t e') with
    | x :: _ -> x
    | _ -> e'