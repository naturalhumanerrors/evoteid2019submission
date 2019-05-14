open Sys

(*	The Caml type theory defined here is the representation of a 
	Tamarin protocol. 
*)

type theory = ident * bodys

and bodys = body list

and body = 
  | IfDef of ident
  | EndIf
  | Sign of sign
  | Rule of rule
  | Restrict of restrict
  | Lemma of lemma

and sign = 
  | Func of functions
  | Eq of equations
  | Built of builtins

and functions = function_sym list
and function_sym = ident * int * bool (* true -> private *)

and equations = equation list
and equation = term * term

and builtins = builtin list
and builtin = 
  | Diffie	
  | Hash			
  | Symenc 		
  | Asymenc 	
  | Signing 		
  | Xor 		
  | Bipair 	
  | Reveal 		
  | Multi

and rule = ident * let_block * facts * (facts option) * facts
and let_block = var_term list
and var_term = msg_var * msetterm
and msg_var = ident * (int option) * bool

and restrict = ident * formula * bool

and lemma = ident * trace_quantifier * formula
and trace_quantifier = 
  | AllTr
  | ExTr

and facts = fact list
and fact = bool * ident * msetterm list

and formula = imp * (imp option)
and imp = 
  | Imp of disjonction 
  | Imp_disj of disjonction * imp
and disjonction = conjonction list
and conjonction = negation list
and negation = bool * atom
and atom = 
  | F
  | T
  | Nested of formula
  | Last of node
  | Action of fact * node
  | Ordering of node * node
  | EqTerm of msetterm * msetterm
  | EqTemp of node * node
  | Quantified of quant * (lvar list) * formula
and lvar = 
  | NodeVar of node
and quant = 
  | ExForm
  | AllForm
(* 
and node_var = 
(* This could be contracted to only one line *)
  | Prefix of bool * ident * (int option)
  | Suffix of ident * (int option)
*)
and type_node = 
  | PubNode
  | FreshNode
  | MsgNode
  | TimeNode
and node = ident * (int option) * type_node

and tupleterm = msetterm list
and msetterm = xorterm list
and xorterm = multterm list
and multterm = expterm list
and expterm = term list
and term = 
  | Tuple of tupleterm
  | Mse of msetterm
  | Bin of binary_app
  | Nary of nary_app
  | Lit of literal
(*  | Null of nullary_fun 
and nullary_fun = ident *)
and binary_app = binary_fun * tupleterm * term
and binary_fun = ident
and nary_app = nary_fun * (multterm list)
and nary_fun = ident
and literal = 
  | Id of ident
  | Fr of ident 
  | Node of node
(*
and nonnode_var =
  | PubPref of pubpref
  | PubSuf of pubsuf
  | FrPref of frpref
  | FrSuf of frsuf
  | Mvar of msgvar
and pubpref = bool * ident * (int option)
and pubsuf = ident * (int option)
and frpref = bool * ident * (int option)
and frsuf = ident * (int option)
and nonnode_var =
  | Pub of pub
  | Fresh of fr
  | Mvar of msg_var
and pub = ident * (int option)
and fr = ident * (int option)
*)

and ident = string

(**********************************************************)
(*************** This is the pretty printer ***************)
(**********************************************************)
let rec pretty_printer name_file p =
  let file = open_out name_file in
  pretty_printer_aux file p;
  close_out file
and pretty_printer_aux file p = 
  let (i,b) = p in
  Printf.fprintf file "theory %s\nbegin\n\n" i;
  pretty_printer_bodys file b;
  Printf.fprintf file "\nend\n"
and pretty_printer_bodys file b = match b with
  | [] -> Printf.fprintf file "\n";
  | body::suit -> 
	pretty_printer_body file body;
	Printf.fprintf file "\n";
	pretty_printer_bodys file suit
and pretty_printer_body file b = match b with
  | IfDef i -> Printf.fprintf file "#ifdef %s" i
  | EndIf -> Printf.fprintf file "#endif"
  | Sign s -> pretty_printer_sign file s
  | Rule r -> pretty_printer_rule file r
  | Restrict r -> pretty_printer_restrict file r
  | Lemma l -> pretty_printer_lemma file l
  
(********** SIGN **********)
and pretty_printer_sign file s = match s with
  | Func f -> pretty_printer_func file f
  | Eq e -> pretty_printer_eq file e
  | Built b -> pretty_printer_built file b
(***** FUNC *****)
and pretty_printer_func file f = 
  Printf.fprintf file "functions: ";
  pretty_printer_func_aux file f
and pretty_printer_func_aux file f = match f with
    | [] -> Printf.fprintf file "\n";
    | [fs] -> pretty_printer_func_sym file fs
    | fs::suit -> 
      pretty_printer_func_sym file fs;
      Printf.fprintf file ", ";
      pretty_printer_func_aux file suit
and pretty_printer_func_sym file f = 
  let (i,n,b) = f in
  Printf.fprintf file "%s/%d" i n;
  if b then Printf.fprintf file "[private]"
(***** EQ *****)  
and pretty_printer_eq file e = 
  Printf.fprintf file "equations: ";
  pretty_printer_eq_aux file e
and pretty_printer_eq_aux file e = match e with
    | [] -> Printf.fprintf file "\n";
    | [es] -> pretty_printer_equation file es
    | es::suit -> 
      pretty_printer_equation file es;
      Printf.fprintf file ", ";
      pretty_printer_eq_aux file suit
and pretty_printer_equation file es = 
  let (t1,t2) = es in
  pretty_printer_term file t1;
  Printf.fprintf file " = ";
  pretty_printer_term file t2
(***** BUILD *****)
and pretty_printer_built file b = 
  Printf.fprintf file "builtins: ";
  pretty_printer_built_aux file b
and pretty_printer_built_aux file b = match b with
    | [] -> ()
    | [bs] -> pretty_printer_builtin file bs; Printf.fprintf file "\n"
    | bs::suit -> 
      pretty_printer_builtin file bs;
      Printf.fprintf file ", ";
      pretty_printer_built_aux file suit
and pretty_printer_builtin file b = match b with
  | Diffie -> Printf.fprintf file "diffie-hellman"
  | Hash -> Printf.fprintf file "hashing"		
  | Symenc -> Printf.fprintf file "symmetric-encryption"
  | Asymenc -> Printf.fprintf file "asymmetric-encryption"
  | Signing -> Printf.fprintf file "signing"
  | Xor -> Printf.fprintf file "xor"
  | Bipair -> Printf.fprintf file "bilinear-pairing"
  | Reveal -> Printf.fprintf file "revealing-signing"
  | Multi -> Printf.fprintf file "multiset"

(********** RULE **********)
and pretty_printer_rule file r = 
  let (i,l,f1,f_opt,f2) = r in
  Printf.fprintf file "rule %s:\n" i;
  pretty_printer_let file l;
  Printf.fprintf file "\t[";
  pretty_printer_facts file f1;
  Printf.fprintf file "]\n";
  (match f_opt with
    | None ->  Printf.fprintf file "\t-->\n";
    | Some f ->  
		Printf.fprintf file "\t--["; 
		pretty_printer_facts file f; 
		Printf.fprintf file "]->\n");
  Printf.fprintf file "\t[";
  pretty_printer_facts file f2;
  Printf.fprintf file "]\n";
(***** LET *****)
and pretty_printer_let file l = match l with
  | [] -> ()
  | _ -> 
      Printf.fprintf file "\tlet ";
      pretty_printer_let_aux file l;
      Printf.fprintf file "\tin\n"
and pretty_printer_let_aux file l = match l with
    | [] -> ()
    | [vt] -> 
      pretty_printer_varterm file vt;
      Printf.fprintf file "\n"
    | vt::suit -> 
      pretty_printer_varterm file vt;
      Printf.fprintf file "\n\t\t";
      pretty_printer_let_aux file suit
(***** VAR_TERM *****)
and pretty_printer_varterm file v =  
  let (mv,mt) = v in
  pretty_printer_msgvar file mv;
  Printf.fprintf file " = ";
  pretty_printer_msetterm file mt
(***** MSG_VAR *****)
and pretty_printer_msgvar file mv = 
  let (i,n,b) = mv in
  Printf.fprintf file "%s" i;
  (match n with
    | None -> Printf.fprintf file " ";
    | Some k -> Printf.fprintf file ".%d " k);
  if b then Printf.fprintf file ": msg"

(********** RESTRICTION **********)
and pretty_printer_restrict file r = 
  let (i,f,_) = r in
  Printf.fprintf file "restriction %s:\n" i;
  Printf.fprintf file "\t%c" '"';
  pretty_printer_formula file f;
  Printf.fprintf file "%c\n" '"'

(********** LEMMA **********)
and pretty_printer_lemma file l = 
  let (i,t,f) = l in
  Printf.fprintf file "lemma %s:\n" i;
  (match t with
     | AllTr -> Printf.fprintf file "\tall-traces\n"
     | ExTr -> Printf.fprintf file "\texists-trace\n");
  Printf.fprintf file "\t%c" '"';
  pretty_printer_formula file f;
  Printf.fprintf file "%c\n" '"'

(***** FACTS *****)
and pretty_printer_facts file fs = match fs with
  | [] -> ()
  | [f] -> pretty_printer_fact file f
  | f::suit -> 
      pretty_printer_fact file f; 
      Printf.fprintf file ", "; 
      pretty_printer_facts file suit
and pretty_printer_fact file f = 
  let (b,i,m) = f in
  if b then (Printf.fprintf file "!");
  Printf.fprintf file "%s(" i;
  pretty_printer_fact_aux file m;
  Printf.fprintf file ")"
and pretty_printer_fact_aux file m = match m with
  | [] -> ()
  | [mst] -> pretty_printer_msetterm file mst
  | mst::suit -> 
      pretty_printer_msetterm file mst;
      Printf.fprintf file ", ";
      pretty_printer_fact_aux file suit

(********** FORMULA **********)
and pretty_printer_formula file f = 
  let (i1,i2) = f in 
  match i2 with
    | None -> pretty_printer_imp file i1
    | Some i ->
        pretty_printer_imp file i1;
        Printf.fprintf file " <=> \n\t";
        pretty_printer_imp file i
(***** IMP *****)
and pretty_printer_imp file i = match i with
  | Imp d -> pretty_printer_disj file d
  | Imp_disj (d,ii) ->
      pretty_printer_disj file d;
      Printf.fprintf file " ==> \n\t";
      pretty_printer_imp file ii
(***** DISJ *****)
and pretty_printer_disj file d = match d with
  | [] -> ()
  | [c] -> pretty_printer_conj file c
  | c::suit ->
      pretty_printer_conj file c;
      Printf.fprintf file " | ";
      pretty_printer_disj file suit
(***** CONJ *****)
and pretty_printer_conj file c = match c with
  | [] -> ()
  | [n] -> pretty_printer_neg file n
  | n::suit ->
      pretty_printer_neg file n;
      Printf.fprintf file " & ";
      pretty_printer_conj file suit
(***** NEG *****) 
and pretty_printer_neg file n = 
  let (b,a) = n in
  if b 
  then 
    (match a with
      | Nested _ -> 
		Printf.fprintf file "not "; 
		pretty_printer_atom file a
      | _ -> 
		Printf.fprintf file "not ("; 
		pretty_printer_atom file a; 
		Printf.fprintf file ")")
  else pretty_printer_atom file a
(***** ATOM *****) 
and pretty_printer_atom file a = match a with
  | F -> Printf.fprintf file "F"
  | T -> Printf.fprintf file "T"
  | Nested f -> 
      Printf.fprintf file "("; 
      pretty_printer_formula file f; 
      Printf.fprintf file ")"
  | Last n -> 
      Printf.fprintf file "last ("; 
      pretty_printer_node file n; 
      Printf.fprintf file ")"
  | Action (f,n) ->
      pretty_printer_fact file f; 
      Printf.fprintf file " @ "; 
      pretty_printer_node file n
  | Ordering (n1,n2) ->
      pretty_printer_node file n1; 
      Printf.fprintf file "<"; 
      pretty_printer_node file n2
  | EqTemp (n1,n2) ->
      pretty_printer_node file n1; 
      Printf.fprintf file "="; 
      pretty_printer_node file n2
  | EqTerm (m1,m2) ->
      pretty_printer_msetterm file m1; 
      Printf.fprintf file "="; 
      pretty_printer_msetterm file m2
  | Quantified (q,l,f) ->
      (match q with
         | ExForm -> Printf.fprintf file "Ex"
         | AllForm -> Printf.fprintf file "All");
      pretty_printer_atom_aux file l;
      pretty_printer_formula file f
and pretty_printer_atom_aux file l = match l with
  | [] -> Printf.fprintf file ". "
  | NodeVar n :: suit ->
      Printf.fprintf file " ";
      pretty_printer_node file n;
      pretty_printer_atom_aux file suit

(***** NODE *****)
and pretty_printer_node file n = 
  let (i,k,t) = n in
  (match t with
     | PubNode -> Printf.fprintf file "$%s" i
     | FreshNode -> Printf.fprintf file "~%s" i
     | MsgNode -> Printf.fprintf file "%s" i
     | TimeNode -> Printf.fprintf file "#%s" i);
  match k with
    | None -> ()
    | Some j -> Printf.fprintf file ".%d" j

(********** TUPLETERM **********)
and pretty_printer_tupleterm file t = 
  Printf.fprintf file "<";
  pretty_printer_tupleterm_aux file t;
  Printf.fprintf file " >"
and pretty_printer_tupleterm_aux file t = match t with
  | [] -> ()
  | [mst] ->
      Printf.fprintf file " ";
      pretty_printer_msetterm file mst
  | mst::suit ->
      Printf.fprintf file " ";
      pretty_printer_msetterm file mst;
      Printf.fprintf file ",";
      pretty_printer_tupleterm_aux file suit
(***** MSETTERM *****)
and pretty_printer_msetterm file mst = match mst with
  | [] -> ()
  | [xt] -> pretty_printer_xorterm file xt
  | xt::suit ->
      pretty_printer_xorterm file xt;
      Printf.fprintf file " + ";
      pretty_printer_msetterm file suit
(***** XORTERM *****)
and pretty_printer_xorterm file xt = match xt with
  | [] -> ()
  | [mt] -> pretty_printer_multterm file mt
  | mt::suit ->
      pretty_printer_multterm file mt;
      Printf.fprintf file " XOR ";
      pretty_printer_xorterm file suit
(***** MULTTERM *****)
and pretty_printer_multterm file mt = match mt with
  | [] -> ()
  | [exp] -> pretty_printer_expterm file exp
  | exp::suit ->
      pretty_printer_expterm file exp;
      Printf.fprintf file " * ";
      pretty_printer_multterm file suit   
(***** EXPTERM *****)
and pretty_printer_expterm file exp = match exp with
  | [] -> ()
  | [t] -> pretty_printer_term file t
  | t::suit ->
      pretty_printer_term file t;
      Printf.fprintf file " ^ ";
      pretty_printer_expterm file suit
(***** TERM *****)
and pretty_printer_term file t = match t with 
  | Tuple tuple -> pretty_printer_tupleterm file tuple
  | Mse mst -> 
      Printf.fprintf file "(";
      pretty_printer_msetterm file mst;
      Printf.fprintf file ")"
  | Bin b ->
      let (i,tu,te) = b in
      Printf.fprintf file "%s{" i;
      pretty_printer_tupleterm file tu;
      Printf.fprintf file "}";
      pretty_printer_term file te
  | Nary n ->
      let (i,m) = n in
      Printf.fprintf file "%s(" i;
      pretty_printer_term_aux file m;
      Printf.fprintf file ")"
  | Lit l -> pretty_printer_litteral file l
and pretty_printer_term_aux file m = match m with
  | [] -> ()
  | [mm] -> pretty_printer_multterm file mm
  | mm::suit ->
      pretty_printer_multterm file mm;
      Printf.fprintf file ",";
      pretty_printer_term_aux file suit
(***** LITTERAL *****)
and pretty_printer_litteral file l = match l with
  | Id i -> Printf.fprintf file "'%s'" i
  | Fr i -> Printf.fprintf file "~'%s'" i 
  | Node n -> pretty_printer_node file n
  



