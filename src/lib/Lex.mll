{
open Lexing
open Parse

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
let atom = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read =
  parse
  | white    { read lexbuf }
  | newline  { next_line lexbuf; read lexbuf }
  | num      { NUMERAL (int_of_string (Lexing.lexeme lexbuf)) }
  | "bool"   { BOOL }
  | ":>"     { COLON_ANGLE }
  | "->"     { RIGHT_ARROW }
  | "@"      { AT }
  | "*"      { STAR }
  | "#"      { HASH }
  | "U"      { UNIV }
  | "lam"    { LAM }
  | "cons"   { CONS }
  | "car"    { CAR }
  | "cdr"    { CDR }
  | '('      { LPR }
  | ')'      { RPR }
  | '['      { LSQ }
  | ']'      { RSQ }
  | ':'      { COLON }
  | '='      { EQUALS }
  | atom     { ATOM (Lexing.lexeme lexbuf) }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof      { EOF }