{
  open Lexing
  open Token_tam
  open Str
  
  type error = {
    character: char;
    line: int;
    pos: int;
  }

  exception Unexpected_character of error

  let next_line lexbuf =
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with 
			 pos_bol = lexbuf.lex_curr_p.pos_cnum;
			 pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1 }
}

(**********************************************************)
let letter = ['a'-'z' 'A'-'Z' '_']
let digit  = ['0'-'9']
let ascii  = _ # ['\n' '"']
let blanks = [' ' '\n' '\t']

rule tokenize = parse
  (* skip new lines and update line count (useful for error location) *)
  | '\n' { let _ = new_line lexbuf in tokenize lexbuf }

  (* skip other blanks *)
  | blanks { tokenize lexbuf }

  (* skip comments *)
  | "//" (_ # '\n')* { tokenize lexbuf }
      
  | "/*" { comment lexbuf; tokenize lexbuf }
  
  | '.' (digit+ as lxm)
      { DOTI (int_of_string lxm) :: tokenize lexbuf } 
  
  | "#ifdef" 
      { IFDEF :: tokenize lexbuf }  
      
  | "#endif"
      { ENDIF :: tokenize lexbuf }  
  
  (* characters *)
  | '(' { LP        :: tokenize lexbuf }
  | ')' { RP        :: tokenize lexbuf }
  | '{' { LB        :: tokenize lexbuf }
  | '}' { RB        :: tokenize lexbuf }
  | '[' { LC        :: tokenize lexbuf }
  | ']' { RC        :: tokenize lexbuf }
  | "-->" {ARROW	:: tokenize lexbuf }
  | "--[" {LEFT_A	:: tokenize lexbuf }
  | "]->" {RIGHT_A	:: tokenize lexbuf }
  
  | '+' { PLUS      :: tokenize lexbuf }
(*  | '-' { MINUS     :: tokenize lexbuf } *)
  | '*' { MUL       :: tokenize lexbuf }
  | "XOR" { XOR     :: tokenize lexbuf }
  | '^' { EXP       :: tokenize lexbuf }
  | '<' { LEQ       :: tokenize lexbuf }
  | '>' { GEQ       :: tokenize lexbuf }
  | '=' { EQUAL     :: tokenize lexbuf }
  
  | "<=>" { EQUIV 	:: tokenize lexbuf }
  | "==>" { IMPL 	:: tokenize lexbuf }
  | '|' { OR	 	:: tokenize lexbuf }
  | '&' { AND	 	:: tokenize lexbuf }
  | "not" { NOT 	:: tokenize lexbuf }  
  | 'F' { FALSE 	:: tokenize lexbuf }
  | 'T' { TRUE	 	:: tokenize lexbuf }
  
  | '/' { SLASH     :: tokenize lexbuf } 
  | ',' { COM       :: tokenize lexbuf }
  | '.' { DOT       :: tokenize lexbuf }
  | ':' { COLON     :: tokenize lexbuf }
  | "'" { APOS		:: tokenize lexbuf }
  | '"' { GUIL		:: tokenize lexbuf }
  
  | '~' { TILD 		:: tokenize lexbuf }
  | '$' { DOLLAR 	:: tokenize lexbuf }
  | '!' { BANG		:: tokenize lexbuf }
  | '@' { AT 		:: tokenize lexbuf }
  | '#' { DIESE 	:: tokenize lexbuf }
     
  (* KEYWORD *)
  | "rule" 						{ RULE_KW 			:: tokenize lexbuf }
  | "theory" 					{ THEORY_KW 		:: tokenize lexbuf }
  | "begin" 					{ BEGIN_KW 			:: tokenize lexbuf }
  | "end" 						{ END_KW 			:: tokenize lexbuf }
  | "functions" 				{ FUNCTION_KW 		:: tokenize lexbuf }
  | "equations" 				{ EQUATION_KW 		:: tokenize lexbuf }
  
  | "builtins" 					{ BUILT_KW 			:: tokenize lexbuf }
  | "diffie-hellman" 			{ DIFFIE_KW 		:: tokenize lexbuf }
  | "hashing" 					{ HASH_KW 			:: tokenize lexbuf }
  | "symmetric-encryption" 		{ SYMENC_KW 		:: tokenize lexbuf }
  | "asymmetric-encryption" 	{ ASYMENC_KW 		:: tokenize lexbuf }
  | "signing" 					{ SIGNING_KW 		:: tokenize lexbuf }
  | "xor" 						{ XOR_KW 			:: tokenize lexbuf }
  | "bilinear-pairing" 			{ BIPAIR_KW 		:: tokenize lexbuf }
  | "revealing-signing" 		{ REVEAL_KW 		:: tokenize lexbuf }
  | "multiset" 					{ MULTI_KW 			:: tokenize lexbuf }
  
  | "[private]" 				{ PRIV_KW 			:: tokenize lexbuf }
  | "node" 						{ NODE_KW 			:: tokenize lexbuf }
  | "let" 						{ LET_KW 			:: tokenize lexbuf }
  | "in" 						{ IN_KW 			:: tokenize lexbuf }
  | "msg" 						{ MSG_KW 			:: tokenize lexbuf }
  | "restriction" 				{ RESTRICT_KW 		:: tokenize lexbuf }
  | "axiom" 					{ AXIOM_KW 			:: tokenize lexbuf }
  | "lemma" 					{ LEMMA_KW 			:: tokenize lexbuf }
  | "all-traces" 				{ ALLTR_KW 			:: tokenize lexbuf }
  | "exists-trace" 				{ EXTR_KW 			:: tokenize lexbuf }
  | "pub" 						{ PUB_KW 			:: tokenize lexbuf }
  | "fresh" 					{ FR_KW 			:: tokenize lexbuf }
  | "last"						{ LAST_KW 			:: tokenize lexbuf }
  | "Ex" 						{ EXFORM_KW 		:: tokenize lexbuf }
  | "All" 						{ ALLFORM_KW 		:: tokenize lexbuf }
  
   
  (* other tokens *)
  | letter (letter | digit)* as lxm
      { IDENT lxm :: tokenize lexbuf }
  | (digit+) as lxm
      { INTEGER (int_of_string lxm) :: tokenize lexbuf }
  | "'" blanks* ((letter | digit)* as lxm) blanks* "'"
      { TEXT lxm :: tokenize lexbuf }
  | "~'" blanks* ((letter | digit)* as lxm) blanks* "'"
      { TEXTT lxm :: tokenize lexbuf }
  
  (* end-of-file : end up with the empty stream *)
  | eof
      { [] }

  (* catch errors *)
  | _ as c
    {
      let e = {
          character = c;
          line = lexbuf.lex_curr_p.pos_lnum;
          pos  = lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol;
        }
      in raise (Unexpected_character e)
    }

and comment = parse
	| "*/" { }
	| "\010" | "\013" | "\013\010" { next_line lexbuf; comment lexbuf }
	| eof { }
	| _ { comment lexbuf }
