module S = SMT.Default

(* constraint just an alternate form of an expression *)
type t = AST.expr

let format f : t -> unit = AST.format f

let of_expr : AST.expr -> t = fun e -> e

(* utilities for collapsing constraints *)
let conjunction : t list -> t =
  CCList.fold_left AST.Infix.(&@) AST.Infix.(bool true)

let disjunction : t list -> t =
  CCList.fold_left AST.Infix.(|@) AST.Infix.(bool false)

(* we'll query constraints, and hold answers as such *)
module Answer = struct
  type t =
    | Sat of Value.Model.t
    | Unsat
    | Unknown
  
  let is_unsat : t -> bool = function
    | Unsat -> true
    | _ -> false

  let is_sat : t -> bool = function
    | Sat _ -> true
    | _ -> false

  let is_unknown : t -> bool = function
    | Unknown -> true
    | _ -> false

  let format f : t -> unit = function
    | Sat m -> CCFormat.fprintf f "SAT:@; %a" Value.Model.format m
    | Unsat -> CCFormat.fprintf f "UNSAT"
    | Unknown -> CCFormat.fprintf f "UNKNOWN"
  
  let to_string = CCFormat.to_string format

  let of_solver_answer : S.Answer.t -> t = function
    | S.Answer.Sat m -> Sat (Cata.convert_model m)
    | S.Answer.Unsat -> Unsat
    | S.Answer.Unknown -> Unknown
end

(* checking a constraint just encodes as a S.expr and calls S.check *)
let check (env : Types.Environment.t) : t -> Answer.t = fun c ->
  (* fresh solver every time *)
  let solver = S.Solver.make () in
  (* we need a propositional variable *)
  let p = S.Solver.propositional ("propositional") in
  (* and to encode our constraint *)
  let e = Cata.encode env c in
  (* which we'll assert as follows *)
  let _ = S.Solver.assert_ solver p e in
  S.Solver.check solver |> Answer.of_solver_answer
  
(* checking wrt a theory is just mildly more complicated *)
let check_wrt_theory (env : Types.Environment.t) (theory : Theory.t) : t -> Answer.t = fun c ->
  (* check the first time *)
  match check env c with
    (* somehow sat - add a bunch of axioms and try once more *)
    | Answer.Sat m ->
      let axioms = Theory.concretize env theory c in
      let c' = conjunction (c :: axioms) in
        check env c'
    (* answer unknown - maybe adding more axioms will fix things? *)
    | Answer.Unknown ->
      let axioms = Theory.concretize env theory c in
      let c' = conjunction (c :: axioms) in
        check env c'
    (* unsat - adding more things won't make a difference *)
    | Answer.Unsat -> Answer.Unsat