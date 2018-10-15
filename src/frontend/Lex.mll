{
open Grammar
open Lexing
open RedBasis.Bwd

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
    if !depth = 0 then `Top else `Comment
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
    ("public", PUBLIC);
    ("private", PRIVATE)
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
    { line_comment token lexbuf }
  | "/-"
    { BlockComment.push (); block_comment token lexbuf }
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
  | "import" whitespace
    { read_import (ref Emp) lexbuf }
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


and line_comment kont = parse
  | line_ending
    { new_line lexbuf; kont lexbuf }
  | _
    { line_comment kont lexbuf }

and block_comment kont = parse
  | "/-"
    { BlockComment.push ();
      block_comment kont lexbuf
    }
  | "-/"
    { match BlockComment.pop () with
      | `Top -> kont lexbuf
      | `Comment -> block_comment kont lexbuf }
  | line_ending
    { new_line lexbuf; block_comment kont lexbuf }
  | _
    { block_comment kont lexbuf }


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


and read_import cells = parse
  | atom_initial atom_subsequent*
    { cells := Snoc (!cells, lexeme lexbuf);
      read_import cells lexbuf }
  | "--"
    { line_comment (read_import cells) lexbuf }
  | "/-"
    { BlockComment.push (); block_comment (read_import cells) lexbuf }
  | "."
    { read_import cells lexbuf }
  | line_ending
    { new_line lexbuf;
      IMPORT (Bwd.to_list !cells) }
  | eof
    { IMPORT (Bwd.to_list !cells) }
  | _ { failwith @@ "Invalid path component character: " ^ lexeme lexbuf }
