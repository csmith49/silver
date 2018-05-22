module Utility = struct
  let cart_prod (l : 'a list) (r : 'b list) : ('a * 'b) list =
    CCList.cartesian_product [l; r]
      |> CCList.filter_map (fun xs -> match xs with [a;b] -> Some (a, b) | _ -> None)
end

(* the type --- list of states, start state, delta, accepting states *)
type ('s, 'e) t = {
  states : 's list;
  start : 's;
  delta : ('s, 'e) Graph.t;
  accepting : 's list;
}

(* take one step along the automata *)
let consume_symbol (init : 's) (s : 'e) (a : ('s, 'e) t) : 's list =
  let out_edges = a.delta init in
  let fm = fun (e, v) -> if e == s then Some v else None in
    CCList.filter_map fm out_edges    

(* consumes a word *)
let rec consume (init : 's) (w : 'e list) (a : ('s, 'e) t) : 's list =
  match w with
    | [] -> []
    | s :: ss ->
      let out_states = consume_symbol init s a in
      let step_again = fun i -> consume i ss a in
        CCList.flat_map step_again out_states

(* containment in the language *)
let mem (w : 'e list) (a : ('s, 'e) t) : bool =
  let terminal_states = consume a.start w a in
  let accepting = fun s -> List.mem s a.accepting in
    CCList.exists accepting terminal_states

(* negation *)
let negate : ('s, 'e) t -> ('s, 'e) t = fun a -> 
  let not_accepted = fun s -> not (List.mem s a.accepting) in
    {a with
      accepting = CCList.filter not_accepted a.states;
    }

(* some summary utilities, so we can actually inspect the resulting graphs *)
let summary (np : 's -> string) (ep : 'e -> string) (a : ('s, 'e) t) : string = 
  let local_view = fun v ->
    let v' = np v in
    let d' = CCList.map (fun (e, v) -> "-{" ^ (ep e) ^ "}-> " ^ (np v)) (a.delta v) in
      CCString.concat "\n\t" (v' :: d') in
  let start' = "Start:\n\t" ^ (np a.start) in
  let acc' =
    CCString.concat "\n\t" ("Accepting:" :: (CCList.map np a.accepting)) in
  let divider = "<==================================>" in
  CCString.concat "\n" (start' :: acc' :: divider :: (CCList.map local_view a.states))