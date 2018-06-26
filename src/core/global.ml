(* global state and whatnot *)
let filename = ref "";;
let verbose = ref false;;
let show_auto = ref false;;
let pause = ref false;;

(* command line flags *)
let args = [
  ("-f", Arg.Set_string filename, " Path to .ag file");
  ("-v", Arg.Set verbose, " Enables verbose output");
  ("-a", Arg.Set show_auto, " Enables automata output");
  ("-p", Arg.Set pause, " Enables halting after each iteration");
];;
let anon_fun = fun x -> ();;
let usage_msg = "tbd";;

let get_args () = Arg.parse args anon_fun usage_msg;;
