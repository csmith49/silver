(* alias to make remaining code shorter *)
module I = Parser.MenhirInterpreter

(* exception for when the parse fail *)
exception ParseFailure of string

(* load an ast from a file *)
let rec parse : string -> AST.program = fun filename ->
  let lexbuf = Lexing.from_channel (open_in filename) in
  let checkpoint = Parser.Incremental.program lexbuf.Lexing.lex_curr_p in
  let supplier = I.lexer_lexbuf_to_supplier Lexer.read lexbuf in
    I.loop_handle success (failure lexbuf) supplier checkpoint
and success : AST.program -> AST.program = fun x -> x
and failure lexbuf checkpoint = match checkpoint with
  | I.HandlingError env ->
    let (b, e) = I.positions env in
    let msg = Lexing.sub_lexeme lexbuf b.Lexing.pos_cnum e.Lexing.pos_cnum in
      raise (ParseFailure msg)
  | _ -> raise Exit


let parse_expr : string -> AST.expr = fun s ->
  let lexbuf = Lexing.from_string s in
  let checkpoint = Parser.Incremental.just_expression lexbuf.Lexing.lex_curr_p in
  let supplier = I.lexer_lexbuf_to_supplier Lexer.read lexbuf in
    I.loop supplier checkpoint

let parse_id : string -> AST.id = fun s ->
  let lexbuf = Lexing.from_string s in
  let checkpoint = Parser.Incremental.just_identifier lexbuf.Lexing.lex_curr_p in
  let supplier = I.lexer_lexbuf_to_supplier Lexer.read lexbuf in
    I.loop supplier checkpoint