{
 (* auto-generated by gt *)

open Lsimplify_parse;;

}

rule token = parse
| ['\t' ' ' ]+ { token lexbuf }
| '/' '*' ([^'*']+ | ('*' [^'/'])+)* '*' '/' as str {
   String.iter (fun c -> if c='\n' then Lsimplify_util.line := (!Lsimplify_util.line + 1)) str;
   token lexbuf }
| '-' '-' [^'!']  (_ # '\n')* { token lexbuf }
| ['\n']+ as str { Lsimplify_util.line := (!Lsimplify_util.line + (String.length str)); token lexbuf }
| "--!" { KINDCOMM }
| ".." { DOTDOT }
| "->" { ARROW }
| "=>" { IMPLIES }
| "<>" { DIAMOND }
| "<=" { LTEQUALS }
| ">=" { GTEQUALS }
| "(" { LEFTPAREN }
| ")" { RIGHTPAREN }
| "[" { LEFTSQUARE }
| "]" { RIGHTSQUARE }
| "<" { LESSTHAN }
| ">" { GREATERTHAN }
| "+" { PLUS }
| "*" { STAR }
| "/" { SLASH }
| "^" { UPCARAT }
| "|" { PIPE }
| ";" { SEMICOLON }
| "," { COMMA }
| ":" { COLON }
| "=" { EQUALS }
| "-" { MINUS }
| "#" { POUND }
| "function" { FUNCTION }
| "current" { CURRENT }
| "include" { INCLUDE }
| "returns" { RETURNS }
| "assert" { ASSERT }
| "const" { CONST }
| "else" { ELSE }
| "node" { NODE }
| "step" { STEP }
| "then" { THEN }
| "type" { TYPE }
| "when" { WHEN }
| "with" { WITH }
| "and" { AND }
| "div" { DIV }
| "let" { LET }
| "mod" { MOD }
| "not" { NOT }
| "pre" { PRE }
| "tel" { TEL }
| "var" { VAR }
| "xor" { XOR }
| "if" { IF }
| "or" { OR }
| ['0'-'9']+ '.' ['0'-'9']+ (['e' 'E'] ['+' '-'] ['0'-'9']+)? as str { REAL(str) }
| ['0'-'9']+ as str { INTEGER(str) }
|  ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '\'' '_']*  as str { IDENTIFIER(str) }
|  '"' [^'"']* '"' as str { STRINGLIT(str) }
| eof { EOF }
| _ {failwith("syntax error in "^(!Lsimplify_util.file)^" on line "^(string_of_int !Lsimplify_util.line)^" near '"^(Lexing.lexeme lexbuf)^"'")}{}
