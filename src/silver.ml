(* we'll need this eventually, but this is just to make sure it's included in the build process for now *)
open Check
open Interpolant

(* get the cmd line args *)
let _ = Global.get_args ();

(* let's do some parsing *)
let program = Parse.parse !Global.filename in
let pre, ast, post = program in
let env = Static.global_context program |> CCOpt.get_exn in
let automata = Program.of_ast ast in

(* minor summary info *)
print_endline "[AUTOMATA SUMMARY]";
print_endline (Program.to_string automata);
print_endline "";
print_endline "[ENVIRONEMNT]";
print_endline (Types.Environment.to_string env);
print_endline "";

(* the abstraction we'll be adding proofs to *)
let abstraction = ref Abstraction.init in
let finished = ref false in

let strategy = Trace.vars_in_scope in
let d_axioms = Probability.Laplace.all in

let _ = print_endline "[TRACES]" in

while (not !finished) do
  let _ = print_endline ("[ABSTRACTION] Current abstraction is: ") in
  let _ = print_endline (Abstraction.to_string !abstraction) in
  (* STEP 1: Check to see if our abstraction covers the program automata *)
  match Abstraction.covers ~verbose:!Global.verbose automata !abstraction with
    (* CASE 1.1: The automata is covered. The abstraction serves as a proof that p is correct *)
    | Abstraction.Covers -> begin 
        finished := true;
        print_endline "[DONE] Automata covered. Program is correct.";
      end
    (* CASE 1.2: There is some path in the program not covered by the abstraction *)
    | Abstraction.Counterexample path ->
      let _ = print_endline ("[TRACE FOUND] " ^ (Trace.path_to_string path)) in
      (* STEP 2: check if the path satisfies the post-condition *)
      let answer = Check.check ~verbose:!Global.verbose env strategy d_axioms pre path post in
      match answer with
        (* CASE 2.1: the path cannot be proven to be correct - return as a counterexample *)
        | None -> begin
            finished := true;
            print_endline "[DONE] Program incorrect. Counter-example found.";
            print_endline ("[COUNTEREXAMPLE] " ^ (path
              |> Graph.Path.to_word
              |> CCList.map Program.Label.to_string
              |> CCString.concat "; "
            ));
          end
        (* CASE 2.2: the path is correct - we need to convert evidence of such to a proof *)
        | Some _ -> begin
            print_endline "[TRACE CORRECT] Generating proof.";
            (* STEP 3: refine the proof *)
            abstraction := Abstraction.add (Abstraction.of_path path) !abstraction;
            print_endline "[TRACE ADDED] Iterating...";
          end
done;
