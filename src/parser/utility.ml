(* alias to make remaining code shorter *)
module I = Parser.MenhirInterpreter

(* exception for when the parse fail *)
exception ParseFailure of string

(* load an ast from a file *)
let rec parse : string -> AST.t = fun filename ->
  let lexbuf = Lexing.from_channel (open_in filename) in
  let checkpoint = Parser.Incremental.program lexbuf.Lexing.lex_curr_p in
  let supplier = I.lexer_lexbuf_to_supplier Lexer.read lexbuf in
    I.loop_handle success (failure lexbuf) supplier checkpoint
and success : AST.t -> AST.t = fun x -> x
and failure lexbuf checkpoint = match checkpoint with
  | I.HandlingError env ->
    let (b, e) = I.positions env in
    let msg = Lexing.sub_lexeme lexbuf b.Lexing.pos_cnum e.Lexing.pos_cnum in
      raise (ParseFailure msg)
  | _ -> raise Exit
