(** The type of binary operators. *)
type bop = 
  | Add
  | Mult
  | Leq

(** The type of the abstract syntax tree (AST). *)
type expr =
  | Var of string
  | Int of int
  | Bool of bool  
  | Binop of bop * expr * expr
  | Call of string * expr array
  | Let of string * expr * expr
  | Def of string * string array * expr * expr
  | If of expr * expr * expr
