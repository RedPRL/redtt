{
open Grammar
open Lexing

let make_table num elems =
  let table = Hashtbl.create num in
  List.iter (fun (k, v) -> Hashtbl.add table k v) elems;
  table


module BlockComment =
struct
  let depth = ref 0

  let push () =
    depth := !depth + 1

  let pop () =
    depth := !depth - 1;
    if !depth = 0 then `Token else `Comment
end

let keywords =
  make_table 0 [
    ("V", V);
    ("opaque", OPAQUE);
    ("print", PRINT);
    ("check", CHECK);
    ("quit", QUIT);
    ("in", IN);
    ("with", WITH);
    ("where", WHERE);
    ("data", DATA);
    ("begin", BEGIN);
    ("end", END);
    ("tick", TICK);
    ("✓", TICK);
    ("meta", META);
    ("dim", DIM);
    ("𝕀", DIM);
    ("⊢", RIGHT_TACK);
    ("elim", ELIM);
    ("fst", FST);
    ("snd", SND);
    ("coe", COE);
    ("com", COM);
    ("pair", PAIR);
    ("hcom", HCOM);
    ("comp", COMP);
    ("vproj", VPROJ);
    ("vin", VIN);
    ("let", LET);
    ("fun", FUN);
    ("def", DEF);
    ("lam", LAM);
    ("next", NEXT);
    ("prev", PREV);
    ("dfix", DFIX);
    ("fix", FIX);
    ("call", CALL);
    ("refl", REFL);
    ("pre", PRE);
    ("kan", KAN);
    ("U", UNIV);
    ("debug", DEBUG);
    ("normalize", NORMALIZE);
    ("type", TYPE);
    ("import", IMPORT);
  ]
}

let line_ending
  = '\r'
  | '\n'
  | "\r\n"
let number =
  ['0'-'9']+
let whitespace =
  [' ' '\t']+
let atom_initial =
  [^ '0'-'9' '-' '?' '!' '(' ')' '[' ']' '{' '}' '<' '>' '.' '#' '\\' '@' '*' '^' ':' ',' ';' '|' '=' '"' '`' ' ' '\t' '\n' '\r']
let atom_subsequent =
  [^                     '(' ')' '[' ']' '{' '}' '<' '>' '.' '#' '\\' '@' '*' '^' ':' ',' ';' '|' '=' '"' ' ' '\t' '\n' '\r']

rule token = parse
  | number
    { NUMERAL (int_of_string (Lexing.lexeme lexbuf)) }
  | "--"
    { line_comment lexbuf }
  | "/-"
    { BlockComment.push (); block_comment lexbuf }
  | '('
    { LPR }
  | ')'
    { RPR }
  | '['
    { LSQ }
  | ']'
    { RSQ }
  | '{'
    { LBR }
  | '}'
    { RBR }
  | '#'
    { HASH }
  | "⦉"
    { LTR }
  | "⦊"
    { RTR }
  | "<:"
    { LTR }
  | ":>"
    { RTR }
  | "«"
    { LLGL }
  | "<<"
    { LLGL }
  | "»"
    { RRGL }
  | ">>"
    { RRGL }
  | '!'
    { BANG }
  | '@'
    { AT }
  | '`'
    { BACKTICK }
  | "!-"
    { RIGHT_TACK }
  | '|'
    { PIPE }
  | '^'
    { CARET }
  | '*'
    { AST }
  | "×"
    { TIMES }
  | ':'
    { COLON }
  | ';'
    { SEMI }
  | ','
    { COMMA }
  | '.'
    { DOT }
  | "∂"
    { BOUNDARY }
  | ":>"
    { TRIANGLE_RIGHT }
  | "▷"
    { TRIANGLE_RIGHT }
  | '='
    { EQUALS }
  | "->"
    { RIGHT_ARROW }
  | "→"
    { RIGHT_ARROW }
  | "<"
    { LGL }
  | ">"
    { RGL }
  | "λ"
    { LAM }
  | "\\"
    { LAM }
  | '"'
    { read_string (Buffer.create 17) lexbuf }
  | line_ending
    { new_line lexbuf; token lexbuf }
  | whitespace
    { token lexbuf }
  | eof
    { EOF }
  | "?" atom_initial atom_subsequent*
    {
      match String.split_on_char '?' @@ lexeme lexbuf with
      | [] ->
        Grammar.HOLE_NAME None
      | _ :: input ->
        let name = String.concat "" input in
        Grammar.HOLE_NAME (Some name)
    }
  | "?"
    { (Grammar.HOLE_NAME None) }
  | atom_initial atom_subsequent*
    {
      let input = lexeme lexbuf in
      begin try
        let kwd = Hashtbl.find keywords input in
        kwd
      with Not_found ->
        Grammar.ATOM input
      end
    }
  | _
    { Format.eprintf "Unexpected char: %s" (lexeme lexbuf);
      failwith "Lexing error" }

and line_comment = parse
  | line_ending
    { new_line lexbuf; token lexbuf }
  | _
    { line_comment lexbuf }

and block_comment = parse
  | "/-"
    { BlockComment.push ();
      block_comment lexbuf
    }
  | "-/"
    { match BlockComment.pop () with
      | `Token -> token lexbuf
      | `Comment -> block_comment lexbuf }
  | line_ending
    { new_line lexbuf; block_comment lexbuf }
  | _
    { block_comment lexbuf }


(* from https://v1.realworldocaml.org/v1/en/html/parsing-with-ocamllex-and-menhir.html *)
and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { failwith (("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { failwith ("String is not terminated") }


