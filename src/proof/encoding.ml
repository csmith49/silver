(* we first will convert traces to ssa *)
module VarCounter = struct
  open Name.Infix
  
  module NameMap = CCMap.Make(Name)

  type t = int NameMap.t

  let initial : t = NameMap.empty

  let get_count (n : Name.t) (c : t) : int =
    NameMap.get_or ~default:0 n c

  let increment (n : Name.t) (c : t) : t =
    let count = get_count n c in
    NameMap.add n (count + 1) c

  (* some helpers for dealing with identifiers *)
  let get_name : AST.id -> Name.t = function
    | AST.Var n -> n
    | AST.IndexedVar (n, _) -> n

  let update_name (n : Name.t) : AST.id -> AST.id = function
    | AST.Var _ -> AST.Var n
    | AST.IndexedVar (_, e) -> AST.IndexedVar (n, e)

  let update_id (i : AST.id) (c : t) : AST.id =
    let n = get_name i in
    let count = get_count n c in
    let n' = n <+ (string_of_int count) in
      (update_name n' i)

  let rec update (e : AST.expr) (c : t) : AST.expr = match e with
    | AST.Literal _ -> e
    | AST.Identifier i ->
      AST.Identifier (update_id i c)
    | AST.BinaryOp (o, l, r) -> AST.BinaryOp (o, update l c, update r c)
    | AST.UnaryOp (o, e) -> AST.UnaryOp (o, update e c)
    | AST.FunCall (f, args) -> AST.FunCall (f, CCList.map (fun e -> update e c) args)
end

let rec ssa ?(counter=VarCounter.initial) : Trace.t -> Trace.t = function
  | [] -> []
  | (s, l, d) :: rest -> 
    let counter, edge = match l with
      | Program.Edge.Assign (i, e) ->
        let e' = VarCounter.update e counter in
        let counter = VarCounter.increment (VarCounter.get_name i) counter in
        let i' = VarCounter.update_id i counter in
          (counter, (s, Program.Edge.Assign (i', e'), d))
      | Program.Edge.Draw (i, e) ->
        let e' = VarCounter.update e counter in
        let counter = VarCounter.increment (VarCounter.get_name i) counter in
        let i' = VarCounter.update_id i counter in
          (counter, (s, Program.Edge.Draw (i', e'), d))
      | Program.Edge.Assume e ->
        (counter, (s, Program.Edge.Assume (VarCounter.update e counter), d))
    in edge :: (ssa ~counter:counter rest)