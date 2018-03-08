{
open Lexing
open Token

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let num = ['0'-'9'] ['0'-'9']*
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let atom = "->" | "*" | ['a'-'z' 'A'-'Z' '_' ':' '+'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

(* part 4 *)
rule read =
  parse
  | white    { read lexbuf }
  | newline  { next_line lexbuf; read lexbuf }
  | num      { NUMERAL (int_of_string (Lexing.lexeme lexbuf)) }
  | atom     { ATOM (Lexing.lexeme lexbuf) }
  | '('      { LEFT_PAREN }
  | ')'      { RIGHT_PAREN }
  | '['      { LEFT_SQUARE }
  | ']'      { RIGHT_SQUARE }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof      { EOF }