(* we'll need this eventually, but this is just to make sure it's included in the build process for now *)
open Check
open Interpolant
open Merge

open CCFormat

(* get the cmd line args *)
let _ = Global.get_args ();

(* let's do some parsing *)
let program = Parse.parse !Global.filename in
let pre, ast, post, cost = program in
let env = Static.global_context program |> CCOpt.get_exn in
let automata = Program.of_ast ast in

(* minor summary info *)
printf "@[<v>[AUTOMATA SUMMARY]@;%a@;[ENVIRONMENT]@;%s@;" 
  (DFA.format Program.State.format Program.Label.format) automata
  (Types.Environment.to_string env);

(* the abstraction we'll be adding proofs to *)
let abstraction = ref Abstraction.init in
let finished = ref false in

let strategy = Trace.beta_strat in
let d_axioms = Probability.Laplace.all @ Probability.Bernoulli.all in

let _ = printf "[TRACES]@]@." in

while (not !finished) do
  (* handle pausing if we want to *)
  let _ = if !Global.pause then 
    let _ = CCFormat.print_newline () in
    read_line ()
  else "" in
  (* start printing *)
  let _ = printf "@[" in
  (* if abstraction printing enabled, show current abstraction after each round *)
  let _ = if !Global.show_auto then begin
    match Abstraction.Conjunction.of_abstraction !abstraction with
      | Some abs -> 
          printf "@[<v>[ABSTRACTION] Current abstraction is: @;%a@;@]" 
            (DFA.format 
              (CCFormat.list ~sep:(CCFormat.return " | ") Abstraction.State.format) 
              Abstraction.Label.format)
            abs
      | None -> printf "@[<v>[ABSTRACTION] Current abstraction is: @;Empty@;@]"
    end
  else () in
  (* STEP 1: Check to see if our abstraction covers the program automata *)
  match Abstraction.covers ~verbose:!Global.verbose automata !abstraction with
    (* CASE 1.1: The automata is covered. The abstraction serves as a proof that p is correct *)
    | Abstraction.Covers -> begin 
        finished := true;
        printf "[DONE] Automata covered. Program is correct.";
      end
    (* CASE 1.2: There is some path in the program not covered by the abstraction *)
    | Abstraction.Counterexample path ->
      let _ = CCFormat.printf "@[<v>[TRACE FOUND]@ @[%a@]@;@]" Trace.format_path path in
      (* STEP 2: check if the path satisfies the post-condition *)
      let proofs = Check.check ~verbose:!Global.verbose env strategy d_axioms pre path post cost in
      begin match proofs with
        (* CASE 2.1: the path cannot be proven to be correct - return as a counterexample *)
        | [] -> begin
            finished := true;
            printf "@[<v 4>[DONE] Program incorrect. Counter-example found.@;@[<v>%a@]@;@]"
              (CCFormat.list ~sep:(CCFormat.return ";@;") Program.Label.format) 
              (path |> Graph.Path.to_word);
          end
        (* CASE 2.2: the path is correct - we need to convert evidence of such to a proof *)
        | proof :: _ -> begin
            printf "[TRACE CORRECT] Generating proof.@;";
            (* STEP 3: refine the proof *)
            abstraction := Abstraction.add proof !abstraction;
            printf "[TRACE ADDED] Iterating...@;";
          end
        end
    | Abstraction.Unknown -> ();
  printf "@]@.";
done;
CCFormat.print_newline ();