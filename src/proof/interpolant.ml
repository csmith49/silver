(* we'll end up doing some direct manipulation of formulae *)
module S = SMT.Default

(* an interpolant is just a constraint - we maintain our ast and the logical encoding *)
type interpolant = Constraint.conjunction

(* for sequence interpolants, our conditions are all in the form of validity of implications *)
(* that is, we wish to compute validity of A => S *)
let impl_validity (ante : Constraint.conjunction) (succ : Constraint.conjunction) : bool =
  (* negate the succedent *)
  let negate s = {
    Constraint.expression = AST.Infix.(!.) s.Constraint.expression;
    encoding = S.Expr.not s.Constraint.encoding;
  } in
  (* construct the formula A & !S *)
  let formula = ante @ (CCList.map negate succ) in
  match Constraint.check formula with
    (* valid iff A & !S unsat *)
    | Constraint.Answer.Unsat -> true
    | _ -> false

(* infix version, because I can't stop *)
let ( => ) (ante : Constraint.conjunction) (succ : Constraint.conjunction) : bool = 
  impl_validity ante succ

(* surprisingly, don't have false as a default constraint *)
let c_false = Constraint.of_expr Types.Environment.empty (AST.Literal (AST.Boolean false))

(* the only other condition relies on the free variables used *)
module Variables = struct
  type t = AST.id

  let rec free : AST.expr -> t list = function
    | AST.Literal _ -> []
    | AST.Identifier i -> begin match i with
        | AST.IndexedVar (_, e) -> i :: (free e)
        | _ -> [i]
      end
    | AST.FunCall (f, args) ->
      if Operation.is_quantifier f then match args with
        | [AST.Identifier i; e] -> CCList.remove (=) i (free e)
        | _ -> []
      else CCList.flat_map free args

  let intersect (left : t list) (right : t list) : t list = left
    |> CCList.filter (fun l -> CCList.mem (=) l right)
end

(* we can now work on generating sequence interpolants *)
type sequence = interpolant list
type encoding = Trace.encoding

(* generalization using dd *)
let generalize (ante : Constraint.conjunction) (i : interpolant) (succ : Constraint.conjunction) : interpolant =
  let check = fun i -> impl_validity (ante @ i) succ in
  let module I = Delta.Make(struct type t = Constraint.t let check = check end) in
    I.ddmin i

(* pair up sequential elements of a list *)
let drop_first = CCList.tl
let drop_last = CCList.remove_at_idx (-1)

let pairs (xs : 'a list) : ('a * 'a) list =
  let left = drop_last xs in
  let right = drop_first xs in
    CCList.combine left right

(* checking the conditions *)
(* we assume condition 4 guaranteed during generation *)
let check : encoding -> sequence -> bool = fun enc -> fun seq ->
  (* condition 1 *)
  if not ([CCList.hd enc] => (CCList.hd seq)) then false else
  (* condition 2 *)
  if not ((seq |> CCList.last_opt |> CCOpt.get_exn) => [c_false]) then false else
  (* condition 3 *)
  CCList.for_all (fun (phi, (psi1, psi2)) -> (phi:: psi1) => psi2)
    (CCList.combine (drop_first enc) (pairs seq))

(* we'll parameterize generation of sequence interpolants by a strategy *)
module Strategy = struct
  type t = S of (Types.Environment.t -> Variables.t list -> interpolant list)

  let apply = function
    S s -> s
end

(* for accumulating variables *)
let accumulate (f : 'a -> 'a -> 'a) : 'a list -> 'a list = function
  | [] -> []
  | x :: [] -> [x]
  | x :: xs -> CCList.scan_left f x xs

let rev_accumulate (f : 'a -> 'a -> 'a) : 'a list -> 'a list = fun xs -> xs
  |> CCList.rev
  |> accumulate f
  |> CCList.rev

(* now using strategies in a naive way *)
let naive
  (strat : Strategy.t)
  (env : Types.Environment.t)
  (trace : Trace.encoding) : sequence option = 
    let vars_at_stage = trace
      |> CCList.map (fun c -> c.Constraint.expression |> Variables.free) in
    let variables = CCList.combine (accumulate (@) vars_at_stage) (rev_accumulate (@) vars_at_stage)
      |> CCList.map (fun (l, r) -> Variables.intersect l r) in
    let s = Strategy.apply strat env in
    let possibilities = variables
      |> CCList.map s
      |> CCList.cartesian_product in
    CCList.find_opt (check trace) possibilities