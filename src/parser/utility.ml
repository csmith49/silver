(* load an ast from a file *)
let parse : string -> AST.t = fun filename ->
  let lexbuf = Lexing.from_channel (open_in filename) in
  let checkpoint = Parser.Incremental.program lexbuf.Lexing.lex_curr_p in
  let supplier = Parser.MenhirInterpreter.lexer_lexbuf_to_supplier Lexer.read lexbuf in
    Parser.MenhirInterpreter.loop supplier checkpoint