open Static
open Graph
open Abstraction

(* global state and whatnot *)
let filename = ref "";;

(* command line flags *)
let args = [
  ("-f", Arg.Set_string filename, "tbd")
];;
let anon_fun = fun x -> ();;
let usage_msg = "tbd";;

(* parsing with errors present *)


(* the main entry point *)
Arg.parse args anon_fun usage_msg;

(* let's do some parsing *)
(* load the file into a lexing buffer *)
let prog = Utility.parse !filename in
let pre, p, post = prog in
let automata = Program.of_ast p in

print_endline (Program.summary automata);