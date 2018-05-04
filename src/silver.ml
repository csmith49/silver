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
let ast = Utility.parse !filename in 

print_endline (AST.to_string ast);
