{ 
  open Parse;;
  let comment_level = ref 0;;
  let print_comment_level () = ()
(*    print_string"comment_level= "; print_int !comment_level; print_string" "; flush stdout;; *)
  let incr_comment_level () =
    incr comment_level; print_comment_level();;
  let decr_comment_level () =
    decr comment_level; print_comment_level();;
}

let id = ['a'-'z' 'A'-'Z']['0'-'9' '_' 'a'-'z' 'A'-'Z' ]*
let non_neg = ['0'-'9']+
let ws = ['\t' ' ' ]+
let non_nl = (_ # '\n')
let not_comment_delimiter = ((non_nl # ['*' '(']) | ('*' (non_nl # ')')) | ('(' (non_nl # '*')))*

rule token = parse
  | ws { token lexbuf }
  | "char" { CHAR }
  | "->" { ARROW }
  | ":" { COLON }
  | "=" { EQUALS }
  | "left" { LEFT }
  | "right" { RIGHT }
  | ">=" { GTE }
  | "[" { LSQR_BRACKET }
  | "]" { RSQR_BRACKET } 
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "," { COMMA } 
  | "{" { LCURLY }
  | "}" { RCURLY }
  | "*" { TIMES }
  | "+" { PLUS }
  | "line_comment" { LINECOMMENT }  
  | non_neg as str { NONNEG(str) } 
  | "{{" { quoted lexbuf  }
  | '\n'* as str "(*" { Util.line := !Util.line + (String.length str); incr_comment_level(); comment lexbuf }
  | "\"" { iquoted lexbuf  }
  | id as str { ID(str) }
  | '\n'+ as str { Util.line := !Util.line + (String.length str); NEWLINE }
  | "}}" { END_QUOTED }
  | eof { EOF }
  | _ {failwith((Lexing.lexeme lexbuf) ^ 
       ": lexing error on line "^ (string_of_int !Util.line))}
and quoted = parse
  | ((_ # '}') | ('}' (_ # '}')))+ as str { QUOTED(str) }
  | "}}" { END_QUOTED }
and iquoted = parse
  | ((non_nl # ['\\' '"']) | ('\\' '\\') | ('\\' '"'))+"\"" as str { IQUOTED("\""^str) }
and comment = parse
  | not_comment_delimiter "(*" { incr_comment_level(); 
			      comment lexbuf  }
  | not_comment_delimiter "*)" { decr_comment_level();
                              if (!comment_level == 0) 
			      then token lexbuf 
			      else comment lexbuf
			    }
  | not_comment_delimiter '\n' { incr Util.line; comment lexbuf }
{
}
