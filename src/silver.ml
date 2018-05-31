open Static
open Graph

open Synth
open Encoding
open Theory

(* global state and whatnot *)
let filename = ref "";;
let expression = ref "";;

(* command line flags *)
let args = [
  ("-f", Arg.Set_string filename, "tbd");
  ("-e", Arg.Set_string expression, "tbd")
];;
let anon_fun = fun x -> ();;
let usage_msg = "tbd";;

(* parsing with errors present *)


(* the main entry point *)
Arg.parse args anon_fun usage_msg;

(* let's do some parsing *)
(* load the file into a lexing buffer *)
(* let prog = Utility.parse !filename in
let pre, p, post = prog in
let automata = Program.of_ast p in

print_endline (Program.summary automata);
print_endline (("int", "lap(float) + int") |> Synth.mk |> pattern_to_string); *)

if !expression != "" then
  let _ = print_endline "Parsing expression..." in
  let e = Utility.parse_expr !expression in
  let _ = print_endline ("\tExpression: " ^ (AST.expr_to_string e)) in
  let c = CCOpt.get_exn (Static.expression_context e) in
  let _ = print_endline ("\tContext: " ^ (Types.Environment.to_string c)) in
  let _ = print_endline ("Checking SAT...") in
  let f = Constraint.of_expr c e in
  let answer = Constraint.check [f] in
  let _ = print_endline ("\tResult: " ^ (Constraint.Answer.to_string answer)) in
  ()

else ();