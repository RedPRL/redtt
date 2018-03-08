type token =
  | LEFT_PAREN
  | RIGHT_PAREN
  | LEFT_SQUARE
  | RIGHT_SQUARE
  | NUMERAL of int
  | ATOM of string
  | EOF