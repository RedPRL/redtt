%{
  let make_node start stop con = 
    PTm.(Node {info = (start, stop); con = con})
%}

%token <int> NUMERAL
%token <string> ATOM
%token LEFT_SQUARE
%token RIGHT_SQUARE
%token LEFT_PAREN
%token RIGHT_PAREN
%token COLON
%token EQUALS
%token EOF

%start <PTm.t option> prog
%%
prog:
  | e = expr 
    { Some e }
  | EOF
    { None }
  ;

expr:
  | LEFT_PAREN; xs = list(expr); RIGHT_PAREN
    { make_node $startpos $endpos @@ PTm.List xs }
  | a = ATOM
    { make_node $startpos $endpos @@ PTm.Atom a }
  | COLON
    { make_node $startpos $endpos @@ PTm.Atom ":" }
  | EQUALS
    { make_node $startpos $endpos @@ PTm.Atom "=" }
  | n = NUMERAL
    { make_node $startpos $endpos @@ PTm.Numeral n }
  | LEFT_SQUARE; x = ATOM; RIGHT_SQUARE; e = expr
    { make_node $startpos $endpos @@ PTm.Bind (x, e) }
  | LEFT_SQUARE; x = ATOM; COLON; ty = expr; RIGHT_SQUARE; e = expr
    { make_node $startpos $endpos @@ PTm.TyBind (x, ty, e) }
  | LEFT_SQUARE; r0 = expr; EQUALS; r1 = expr; e = expr; RIGHT_SQUARE
    { make_node $startpos $endpos @@ PTm.Tube (r0, r1, e) }
  ;