(* global state and whatnot *)
let filename = ref "";;
let expression = ref "";;
let verbose = ref false;;

(* command line flags *)
let args = [
  ("-f", Arg.Set_string filename, "tbd");
  ("-e", Arg.Set_string expression, "tbd");
  ("-v", Arg.Set verbose, "tbd")
];;
let anon_fun = fun x -> ();;
let usage_msg = "tbd";;

let get_args () = Arg.parse args anon_fun usage_msg;;

let vprint (s : string) : unit = if !verbose then print_endline s else ();;