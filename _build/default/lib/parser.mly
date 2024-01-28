%{
open Ast
%}

%token <int> INT
%token <string> ID
%token TRUE
%token FALSE
%token LEQ
%token TIMES  
%token PLUS
%token COMMA
%token LPAREN
%token RPAREN
%token LET
%token EQUALS
%token IN
%token IF
%token THEN
%token ELSE
%token DEFINE
%token END
%token EOF

%nonassoc IN
%nonassoc ELSE
%left LEQ
%left PLUS
%left TIMES  

%start <Ast.expr> prog

%%

prog:
	| e = expr; END { e }
    | e = expr; EOF { e }
	;
	
expr:
	| i = INT { Int i }
	| x = ID { Var x }
	| TRUE { Bool true }
	| FALSE { Bool false }
	| e1 = expr; LEQ; e2 = expr { Binop (Leq, e1, e2) }
	| e1 = expr; TIMES; e2 = expr { Binop (Mult, e1, e2) } 
	| e1 = expr; PLUS; e2 = expr { Binop (Add, e1, e2) }
	| LET; x = ID; EQUALS; e1 = expr; IN; e2 = expr { Let (x, e1, e2) }
	| DEFINE; x = ID; LPAREN; pa = params; RPAREN; EQUALS; e1 = expr; IN; e2 = expr { Def (Prototype(x, (Array.of_list pa)), e1, e2) }
	| IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr { If (e1, e2, e3) }
	| LPAREN; e=expr; RPAREN {e} 
    | x = ID; LPAREN; ar = args; RPAREN { Call (x, (Array.of_list ar))} 
	;

params:
    vl = separated_list(COMMA, ID) { vl }

args:
    vl = separated_list(COMMA, expr) { vl }
	
