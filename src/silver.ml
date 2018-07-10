(* we'll need this eventually, but this is just to make sure it's included in the build process for now *)
open Interpolant
open CCFormat

(* get the cmd line args *)
let _ = Global.get_args ();

(* let's do some parsing *)
let program = Parse.parse !Global.filename in
let pre, ast, post, cost = program in
let _ = printf "PARSED@." in 
let env = Static.global_context program |> CCOpt.get_exn in
let automata = Program.of_ast ast in

(* minor summary info *)
printf "@[<v>[AUTOMATA SUMMARY]@;%a@;[ENVIRONMENT]@;%s@;" 
  (DFA.format Program.State.format Program.Label.format) automata
  (Types.Environment.to_string env);

(* pick some parameters of the search - these should be controllable from cmd line flags *)
let strategy = Trace.beta_strat in
let d_axioms = Probability.Defaults.all in
let heuristic = History.Heuristic.smallest_abstraction in
let theory = Theory.Defaults.all in

(* instead of maintaining a single abstraction, we maintain a total history *)
let history = ref (History.init heuristic) in
let finished = ref false in

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
        printf "[ABSTRACTION] Current abstraction:@;%a@;----@;%a@;"
          History.format_branch branch
          Abstraction.format abstraction in
      (* STEP 1: Check to see if our abstraction covers the program automata *)
      begin
        (* pop the old branch off the history *)
        history := History.pop !history |> CCOpt.get_exn |> snd;
        (* handle adding *)
        begin match Abstraction.covers ~verbose:(Global.show_intermediate_automata ()) automata abstraction with
          (* CASE 1.1: The automata is covered. The abstraction serves as a proof that p is correct *)
          | Abstraction.Covers -> begin
              printf "[COVERED] Automata covered. Checking costs...@.";
              let abs_cost = Abstraction.cost abstraction in
              if Cost.acceptable env theory pre cost abs_cost then
                begin
                  finished := true;
                  printf "[DONE] Cost is small. Program correct.";
                end
              else
                printf "[COST] Cost is too high. Continuing the search.@.";
            end
          (* CASE 1.2: There is some path in the program not covered by the abstraction *)
          | Abstraction.Counterexample path ->
            let _ = CCFormat.printf "@[<v>[TRACE FOUND]@; @[%a@]@;@]@;" Trace.format_path path in
            (* STEP 2: check if the path satisfies the post-condition *)
            let proofs = Check.check ~verbose:(Global.show_checking ()) env strategy d_axioms pre path post cost in
            begin match proofs with
              (* CASE 2.1: the path can't be shown correct - return as counterexample *)
              | Check.Answer.Incorrect -> begin
                  finished := true;
                  printf "@[<v 4>[DONE] Program incorrect. Counter-example found.@;@[<v>%a@]@;@]"
                    (CCFormat.list ~sep:(CCFormat.return ";@;") Program.Label.format)
                    (path |> Graph.Path.to_word);
                end
              (* CASE 2.2: we've found some proofs *)
              | Check.Answer.Correct proofs -> begin
                  printf "[TRACE CORRECT] Generating proof.@.";
                  (* STEP 3: refine the search *)
                  proofs
                    |> CCList.map (fun proof -> History.Extend.add branch proof)
                    |> CCList.iter (fun branch -> 
                      history := History.add heuristic !history branch);
                end
              | Check.Answer.Unknown ->
                printf "[TRACE UNKNOWN] Cannot prove trace correct - but it might be!@.";
            end
          (* if this case triggers, something weird has happened *)
          | Abstraction.Unknown -> begin
              printf "[SKIPPING] Unsure how to handle abstraction. Skipping it.";
            end
        end;
        (* handle greedy merges *)
        (* if not !finished then
          let merges = Merge.merge_abstraction ~verbose:(Global.show_branching ())
            env pre post cost abstraction in
          merges
            |> CCList.map (fun (l, r, proof) -> History.Extend.merge branch l r proof)
            |> CCList.iter (fun branch ->
              history := History.add heuristic !history branch);
        (* handle generalization *)
        if not !finished then
          let gens = Generalize.generalize_abstraction ~verbose:(Global.show_branching ())
            ~interpolant_strategy:Interpolant.overly_specific
            env pre post cost abstraction in
          gens
            |> CCList.map (fun (i, proof) -> History.Extend.generalize branch i proof)
            |> CCList.iter (fun branch ->
              history := History.add heuristic !history branch); *)
      end
    | None -> begin
      finished := true;
      printf "[Done] Search space exhausted.";
  end;
  printf "@]@.";
done;
CCFormat.print_newline ();