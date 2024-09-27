module type CHANGE = sig
  type t
  val check : t list -> bool
end

module Make = functor (C : CHANGE) -> struct
  type changes = C.t list

  (* split a list of changes into two, roughly equal in size *)
  let rec split : changes -> changes * changes = function
    | [] -> [], []
    | x :: rest ->
      let left, right = split rest in
      if (CCList.length left) <= (CCList.length right) then
        x :: left, right
      else
        left, x :: right

  (* main alg *)
  let rec ddmin : changes -> changes = fun c ->
    dd2 c []
  and dd2 (c : changes) (r : changes) : changes =
    if (CCList.length c) = 1 then c
    else let c1, c2 = split c in
    if C.check (c1 @ r) then dd2 c1 r
    else if C.check (c2 @ r) then dd2 c2 r
    else (dd2 c1 (c2 @ r)) @ (dd2 c2 (c1 @ r))
end