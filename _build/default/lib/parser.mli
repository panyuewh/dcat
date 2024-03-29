
(* The type of tokens. *)

type token = 
  | TRUE
  | TIMES
  | THEN
  | RPAREN
  | PLUS
  | LPAREN
  | LET
  | LEQ
  | INT of (int)
  | IN
  | IF
  | ID of (string)
  | FALSE
  | EQUALS
  | EOF
  | END
  | ELSE
  | DEFINE
  | COMMA

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
