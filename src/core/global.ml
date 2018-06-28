(* global state and whatnot *)
let filename = ref "";;
let verbose = ref 0;;
let show_auto = ref false;;
let pause = ref false;;

(* command line flags *)
let args = [
  ("-f", Arg.Set_string filename, " Path to .ag file");
  ("-v", Arg.Set_int verbose, " Sets level of output verbosity");
  ("-a", Arg.Set show_auto, " Enables automata output");
  ("-p", Arg.Set pause, " Enables halting after each iteration");
];;
let anon_fun = fun x -> ();;
let usage_msg = "tbd";;

let get_args () = Arg.parse args anon_fun usage_msg;;

(* from the verbosity level, construct the verbose flags we'll actually use *)
let show_branching : unit -> bool = fun () -> !verbose >= 1;;
let show_checking : unit -> bool = fun () -> !verbose >= 2;;
let show_intermediate_automata : unit -> bool = fun () -> !verbose >= 3;;
