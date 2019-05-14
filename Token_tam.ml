(*
	All the token that are used to represent a tamarin protocol are 
	defined here. What they correspond to can be found in the file 
	lexer.mll.
*)

type token =
  | IDENT of string
  | TEXT of string
  | TEXTT of string
  | INTEGER of int
  | DOTI of int
  | IFDEF
  | ENDIF
  
  | LP
  | RP  
  | LB 
  | RB  
  | LC
  | RC
  | ARROW
  | LEFT_A
  | RIGHT_A	
  
  | PLUS      
  | MINUS     
  | MUL      
  | XOR     
  | EXP       
  | LEQ       
  | GEQ    
  | EQUAL     
  
  | EQUIV 	
  | IMPL 	
  | OR	 	
  | AND	 	
  | NOT 	 
  | FALSE 	
  | TRUE	 	
  
  | SLASH     
  | COM       
  | DOT
  | COLON    
  | APOS
  | GUIL		
  
  | TILD 		
  | DOLLAR 	
  | BANG		
  | AT 		
  | DIESE 	
     
  (* KEYWORD *)
  | RULE_KW 			
  | THEORY_KW 		
  | BEGIN_KW 		
  | END_KW 			
  | FUNCTION_KW 		
  | EQUATION_KW 		
  
  | BUILT_KW 			
  | DIFFIE_KW 	
  | HASH_KW 			
  | SYMENC_KW 		
  | ASYMENC_KW 	
  | SIGNING_KW 		
  | XOR_KW 		
  | BIPAIR_KW 	
  | REVEAL_KW 		
  | MULTI_KW 	
  
  | PRIV_KW
  | NODE_KW		
  | LET_KW 		
  | IN_KW 			
  | MSG_KW 			
  | RESTRICT_KW 		
  | AXIOM_KW 			
  | LEMMA_KW 			
  | ALLTR_KW 			
  | EXTR_KW 		
  | PUB_KW 			
  | FR_KW 			
  | LAST_KW 		
  | EXFORM_KW 	
  | ALLFORM_KW 	
  
