(* we'll need this eventually, but this is just to make sure it's included in the build process for now *)
open Check

(* get the cmd line args *)
let _ = Global.get_args ();

(* let's do some parsing *)
(* load the file into a lexing buffer *)
let prog = Utility.parse !Global.filename in
let pre, p, post = prog in
let env = Static.global_context p |> CCOpt.get_exn in
let automata = Program.of_ast p in

print_endline "[AUTOMATA SUMMARY]";
print_endline (Program.summary automata);
print_endline "";

print_endline "[ENVIRONEMNT]";
print_endline (Types.Environment.to_string env);
print_endline "";

print_endline "[TRACES]";
let path = Automata.get_word automata |> CCOpt.get_exn in
let _ = print_endline ("[TRACE FOUND] " ^ (Program.path_to_string path)) in
let trace = path |> Trace.of_path env in
let encodings = Trace.encode env Trace.vars_in_scope Probability.Laplace.all trace in
CCList.iter (fun e -> print_endline (Trace.encoding_to_string e)) encodings;

(* if !Global.expression != "" then
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

else (); *)