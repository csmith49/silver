(* we'll need this eventually, but this is just to make sure it's included in the build process for now *)
open Check
open Interpolant
open History
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

(* instead of maintaining a single abstraction, we maintain a total history *)
let history = ref History.init in
let finished = ref false in

(* pick some parameters of the search - these should be controllable from cmd line flags *)
let strategy = Trace.beta_strat in
let d_axioms = Probability.Laplace.all @ Probability.Bernoulli.all in
let heuristic = History.Heuristic.default in

let _ = printf "[TRACES]@]@." in

while (not !finished) do
  (* handle pausing if we want to *)
  let _ = if !Global.pause then  let _ = CCFormat.print_newline () in read_line () else "" in
  (* start printing *)
  let _ = printf "@[<v>" in
  (* select the current abstraction *)
  match History.current !history with
    | Some branch ->
      let abstraction = branch.History.abstraction in  
      (* possibly show current abstraction *)
      let _ = if !Global.show_auto then
        printf "[ABSTRACTION] Current abstraction is@;%a@;"
          Abstraction.format abstraction in
      (* STEP 1: Check to see if our abstraction covers the program automata *)
      begin
        (* pop the old branch off the history *)
        history := History.pop !history |> CCOpt.get_exn |> snd;
        (* handle adding *)
        begin match Abstraction.covers ~verbose:!Global.verbose automata abstraction with
          (* CASE 1.1: The automata is covered. The abstraction serves as a proof that p is correct *)
          | Abstraction.Covers -> begin
              finished := true;
              printf "[DONE] Automata covered. Program correct.";
            end
          (* CASE 1.2: There is some path in the program not covered by the abstraction *)
          | Abstraction.Counterexample path ->
            let _ = CCFormat.printf "@[<v>[TRACE FOUND]@; @[%a@]@;@]@;" Trace.format_path path in
            (* STEP 2: check if the path satisfies the post-condition *)
            let proofs = Check.check ~verbose:!Global.verbose env strategy d_axioms pre path post cost in
            begin match proofs with
              (* CASE 2.1: the path can't be shown correct - return as counterexample *)
              | [] -> begin
                  finished := true;
                  printf "@[<v 4>[DONE] Program incorrect. Counter-example found.@;@[<v>%a@]@;@]"
                    (CCFormat.list ~sep:(CCFormat.return ";@;") Program.Label.format)
                    (path |> Graph.Path.to_word);
                end
              (* CASE 2.2: we've found some proofs *)
              | proofs -> begin
                  printf "[TRACE CORRECT] Generating proof.@.";
                  (* STEP 3: refine the search *)
                  proofs
                    |> CCList.map (fun proof -> History.Extend.add branch proof)
                    |> CCList.iter (fun branch -> 
                      history := History.add ~heuristic:heuristic !history branch);
                end
            end
          (* if this case triggers, something weird has happened *)
          | Abstraction.Unknown -> begin
              printf "[SKIPPING] Unsure how to handle abstraction. Skipping it.";
            end
        end;
        (* handle greedy merges *)
        if not !finished then
          let merges = Merge.merge_abstraction ~verbose:!Global.verbose
            env pre post cost abstraction in
          merges
            |> CCList.map (fun (l, r, proof) -> History.Extend.merge branch l r proof)
            |> CCList.iter (fun branch ->
              history := History.add ~heuristic:heuristic !history branch);
        (* handle generalization *)
      end
    | None -> begin
      finished := true;
      printf "[Done] Search space exhausted.";
  end;
  printf "@]@.";
done;
CCFormat.print_newline ();