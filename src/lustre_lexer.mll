{


open Lustre_parser
let linenum = Lus_convert.linenum
let linepos = Lus_convert.linepos
}
rule token = parse
  | "--!PROPERTY" {PROPERTY}
  | "--%METAPROPERTY" [^';']* {METAPROPERTY(
      let s = Lexing.lexeme lexbuf in
      String.sub s 16 ((String.length s) - 16)
     )}
  | "--!MAIN" {MAIN_NODE}
  | "--" ['\n'] {token lexbuf}
  | "--" [^'!' '\n'] [^'\n']* {token lexbuf}
  |  "/*" ([^'*']* ('*' [^'/'])?)* "*/" {
      String.iter (fun x -> if x = '\n' then incr linenum) (Lexing.lexeme lexbuf);
      token lexbuf}
  | "_TO_" ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* {CONVERT_TO(Lexing.lexeme lexbuf)}
  | "_FROM_" ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* {CONVERT_FROM(Lexing.lexeme lexbuf)}
  | "type" {TYPE}
  | ';' {SEMICOLON}
  | '=' {EQUALS}
  | '[' {LSQBRACKET}
  | ']' {RSQBRACKET}
  | "function" {FUNCTION}
  | "returns" {RETURNS}
  | '(' {LPAREN}
  | ')' {RPAREN}
  | ':' {COLON}
  | ',' {COMMA}
  | "int" {INT}
  | "real" {REAL}
  | "bool" {BOOL}
  | "node" {NODE}
  | "let" {LET}
  | "tel" {TEL}
  | '-' {MINUS}
  | '+' {PLUS}
  | '/' {DIV}
  | '*' {MULT}
  | "div" {INTDIV}
  | "mod" {MOD}
  | "true" {TRUE}
  | "false" {FALSE}
  | "not" {NOT}
  | "and" {AND}
  | "xor" {XOR}
  | "or" {OR}
  | "if" {IF}
  | "then" {THEN}
  | "else" {ELSE}
  | "when" {WHEN}
  | "const" {CONST}
  | "current" {CURRENT}
  | "condact" {CONDACT}
  | "condact_reset" {CONDACT}
  | "assert" {ASSERT}
  | "pre" {PRE}
  | "fby" {FBY}
  | "var" {VAR}
  | "->" {ARROW}
  | "=>" {IMPL}
  | "<=" {LTE}
  | ">=" {GTE}
  | '<' {LT}
  | '>' {GT}
  | "<>" {NEQ}
  | "subrange" {SUBRANGE}
  | "of" {OF}
  | ['0'-'9']+ '.' ['0'-'9']+ {FLOAT(Lexing.lexeme lexbuf)}
  | ['0'-'9']+ '.' ['0'-'9']+ 'E' ('+'|'-') ['0'-'9'] ['0'-'9'] {FLOAT(Lexing.lexeme lexbuf)}
  | ['0'-'9']+ {NUM(Lexing.lexeme lexbuf)}
  | '.' {DOT}
  | ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* {SYM(Lexing.lexeme lexbuf)}
  | eof {EOF_TOK}
  | '\n' {incr linenum; linepos := Lexing.lexeme_start lexbuf; token lexbuf}
  | _ {token lexbuf}
