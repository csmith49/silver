{
  open Lexing
  open Parser

  exception SyntaxError of string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- {
      pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1;
    }
}

(* regexes for the non-trivial bits *)
let id = ['a' - 'z' 'A' - 'Z']+
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let int = '-'? ['0' - '9'] ['0' - '9']*

(* the general tokenizing rules *)
rule read = parse
  | white {read lexbuf}
  | newline {next_line lexbuf; read lexbuf}
  | '+' {PLUS}
  | '*' {MULT}
  | '-' {MINUS}
  | '(' {LEFT_PAREN}
  | ')' {RIGHT_PAREN}
  | '[' {LEFT_BRACKET}
  | ']' {RIGHT_BRACKET}
  | "{{" {LEFT_DOUBLE_BRACE}
  | "}}" {RIGHT_DOUBLE_BRACE}
  | '{' {LEFT_BRACE}
  | '}' {RIGHT_BRACE}
  | '/' {DIV}
  | '&' {AND}
  | '|' {OR}
  | '!' {NOT}
  | "==" {EQ}
  | "<=" {LEQ}
  | ">=" {GEQ}
  | '<' {LT}
  | '>' {GT}
  | "while" {WHILE}
  | "if" {IF}
  | "then" {THEN}
  | "else" {ELSE}
  | "in" {IN}
  | "for" {FORALL}
  | "exists" {EXISTS}
  | '.' {PERIOD}
  | '=' {ASSIGN}
  | '~' {DRAW}
  | ',' {COMMA}
  | ';' {SEMICOLON}
  | eof {EOI}
  | id {NAME (Name.of_string (Lexing.lexeme lexbuf))}
  | int {INT (int_of_string (Lexing.lexeme lexbuf))}