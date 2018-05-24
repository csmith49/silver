(* this entire file is just a simple wrapper to make some types easier *)

type t = (Program.Node.t, Program.Edge.t) Graph.Path.t

let to_string : t -> string = Program.path_to_string