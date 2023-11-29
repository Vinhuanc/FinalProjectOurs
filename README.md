project2/lib/dune -> tells dune about the new files

 ./_build/default/bin/main.exe --printback ./parseme.txt                
 ./_build/default/bin/main.exe --printback ./parseme2.txt
 ./_build/default/bin/main.exe --printback ./parseme3.txt

Chapter 9: 

Lexer.mll
(* GUy 
let white = [' ' '\t']+   //space and tab(+)
let digit = ['0'- '9']
let int = '-'?digit+    //make negative sign('-') optional(?)

rule read = 
  parse
  | white { read lexbuf}  //skips the whitespaces and goes toward next stuff
  | "+" { PLUS }
  | "*" { TIMES }
    | "(" { LPAREN }
    | ")" { RPAREN }
  | int { INT (int_of_string (Lexing.lexeme lexbuf) }    // returns string
  | eof {EOF}
*)


Parser.mly
(* Guy
%token <int> INT      //<int> is the OCaml int
%token EOF
%token PLUS
%token TIMES

%left PLUS      //lower precedence
%left TIMES     //higher precedence


%start <Ast.expr> prog    // return expression node as the AST

%%

prog:                     //rule name
  | e=expr; EOF { e }   //parse the entire program until EOF
  ;

expr:               // new rule for parse
  | i= INT {Int i}  // INT(name of the token)  
  | e1=expr; TIMES; e2=expr {Binop(Mult, e1, e2)}
  | e1=expr; PLUS; e2=expr {Binop (Add, e1, e2)}
  | LPAREN; e=expr; RPAREN {e}
*)