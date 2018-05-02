open Parser

let test = " f(x [(2 + z) * 12])"

let parse_string s =
  let lexbuf = Lexing.from_string s in
    Parser.prog Lexer.read lexbuf

let _ = print_string ((AST.expr_to_string (parse_string test)) ^ "\n")
