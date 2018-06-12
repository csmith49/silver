(* we'll need this eventually, but this is just to make sure it's included in the build process for now *)
open Check
open Interpolant

(* get the cmd line args *)
let _ = Global.get_args ();

(* let's do some parsing *)
(* load the file into a lexing buffer *)
let prog = Parse.parse !Global.filename in
let pre, p, post = prog in
let env = Static.global_context prog |> CCOpt.get_exn in
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
let answer = Check.check ~verbose:!Global.verbose env Trace.vars_in_scope Probability.Laplace.all pre path post in
match answer with
  | Some _ -> print_endline "Correct"
  | None -> print_endline "Incorrect"

