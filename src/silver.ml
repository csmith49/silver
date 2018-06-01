(* we'll need this eventually, but this is just to make sure it's included in the build process for now *)
open Trace

(* get the cmd line args *)
let _ = Global.get_args ();

(* let's do some parsing *)
(* load the file into a lexing buffer *)
(* let prog = Utility.parse !filename in
let pre, p, post = prog in
let automata = Program.of_ast p in

print_endline (Program.summary automata);
print_endline (("int", "lap(float) + int") |> Synth.mk |> pattern_to_string); *)

if !Global.expression != "" then
  let _ = print_endline "Parsing expression..." in
  let e = Utility.parse_expr !Global.expression in
  let _ = print_endline ("\tExpression: " ^ (AST.expr_to_string e)) in
  let c = CCOpt.get_exn (Static.expression_context e) in
  let _ = print_endline ("\tContext: " ^ (Types.Environment.to_string c)) in
  let _ = print_endline ("Checking SAT...") in
  let f = Constraint.of_expr c e in
  let answer = Constraint.check_wrt_theory c Theory.Defaults.log [f] in
  let _ = print_endline ("\tResult: " ^ (Constraint.Answer.to_string answer)) in
  ()

else ();