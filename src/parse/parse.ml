open Lexing

let pos_string pos =
  let l = string_of_int pos.pos_lnum
  and c = string_of_int (pos.pos_cnum - pos.pos_bol) in
  "line " ^ l ^ ", column " ^ c

let apply_parser (parser : (lexbuf -> Parser.token) -> lexbuf -> 'a) (source: string) : 'a =
  let lexbuf = Lexing.from_string source in
  try
    parser Lexer.read lexbuf
  with Parser.Error ->
    raise (Failure ("Parse error at " ^ (pos_string lexbuf.lex_curr_p)))

let parse_program = apply_parser Parser.program
let parse_expr = apply_parser Parser.just_expression
let parse_id = apply_parser Parser.just_identifier
