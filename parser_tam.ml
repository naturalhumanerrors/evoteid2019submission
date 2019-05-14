open ASD_tam
open Token_tam

(* p? *)
let opt p = parser
  | [< x = p >] -> Some x
  | [< >] -> None

(* p* *)
let rec many p = parser
  | [< x = p; l = many p >] -> x :: l
  | [< >] -> []

(* p+ *)
let some p = parser
  | [< x = p; l = many p >] -> x :: l

(* p (sep p)* *)
let rec list1 p sep = parser
  | [< x = p; l = list1_aux p sep >] -> x :: l
and list1_aux p sep = parser
  | [< _ = sep; l = list1 p sep >] -> l
  | [< >] -> []

(* (p (sep p)* )* *)
let list0 p sep = parser 
  | [< l = list1 p sep >] -> l
  | [< >] -> []

(***************************************** TAMARIN LANGUAGE *****************************************)
let rec protocol = parser
  | [< 'THEORY_KW; 'IDENT i ?? "Protocol IDENT"; 
	'BEGIN_KW ?? "Protocol BEGIN";  b = bodys; 
	'END_KW ?? "Protocol END">] -> (i,b)

and bodys = parser
  | [< 'IFDEF; 'IDENT i; b = bodys >] -> IfDef(i)::b 
  | [< 'ENDIF; b = bodys >] -> EndIf::b
  | [< s = signature; b = bodys >] -> Sign(s)::b
  | [< r = rul; b = bodys >] -> Rule(r)::b
  | [< r = restr; b = bodys >] -> Restrict(r)::b
  | [< l = lem; b = bodys >] -> Lemma(l)::b
  | [< >] -> []

(******************** SIGNATURE ********************)
and signature = parser
  | [< f = funct >] -> Func(f)
  | [< e = equa >] -> Eq(e)
  | [< b = build >] -> Built(b)

(********** FUNCTION **********)
and funct = parser 
  | [< 'FUNCTION_KW; 'COLON ?? "funct COLON"; 
	f = list1 funct_sym com >] -> f
and funct_sym = parser
  | [< 'IDENT i; 'SLASH ?? "funct_sym slash"; 
	'INTEGER n ?? "funct_sym integer"; 
	p = private_ >] -> (i,n,p)

(********** EQUATION **********)
and equa = parser 
  | [< 'EQUATION_KW; 'COLON ?? "equa COLON"; 
	e = list1 equa_sym com >] -> e
and equa_sym = parser
  | [< t1 = term_; 'EQUAL ?? "equa_sym equal"; 
	t2 = term_ >] -> (t1,t2)

(********** BUILTIN **********)
and build = parser 
  | [< 'BUILT_KW; 'COLON ?? "build COLON"; 
	b = list1 builtins_ com>] -> b
and builtins_ = parser
  | [< 'DIFFIE_KW >] -> Diffie
  | [< 'HASH_KW >] -> Hash
  | [< 'SYMENC_KW >] -> Symenc
  | [< 'ASYMENC_KW >] -> Asymenc
  | [< 'SIGNING_KW >] -> Signing
  | [< 'XOR_KW >] -> Xor
  | [< 'BIPAIR_KW >] -> Bipair
  | [< 'REVEAL_KW >] -> Reveal
  | [< 'MULTI_KW >] -> Multi

(******************** RULE ********************)
and rul = parser
  | [< 'RULE_KW; 'IDENT r ?? "rul IDENT"; 'COLON ?? "rul COLON"; 
	l = let_block_; 'LC ?? "rul LC1"; f1 = facts_; 
	'RC ?? "rul RC1"; f_opt = inter_fact; 'LC ?? "rul LC1"; 
	f2 = facts_; 'RC ?? "rul RC2" >] -> (r,l,f1,f_opt,f2)
and let_block_ = parser
  | [< 'LET_KW; vt = some var_term_; 'IN_KW ?? "let_block end" >] -> vt
  | [< >] -> []
and var_term_ = parser
  | [< m1 = msg_var_; 'EQUAL ?? "var_term_ EQUAL"; 
	m2 = msetterm_ >] -> (m1,m2)
and msg_var_ = parser
  | [< 'IDENT i; n = natural_; b = is_msg_ >] -> (i,n,b) 
and is_msg_ = parser
  | [< 'COLON; 'MSG_KW ?? "is_msg_ end" >] -> true
  | [< >] -> false
and inter_fact = parser 
  | [< 'LEFT_A; f = facts_; 'RIGHT_A ?? "rul IDENT" >] -> Some f
  | [< 'ARROW >] -> None

(******************** RESTRICTION ********************)
and restr = parser
  | [< b = restr_or_ax; 'IDENT i ?? "restr IDENT"; 
	'COLON ?? "restr COLON"; 'GUIL ?? "restr GUIL1"; f = formula_; 
	'GUIL ?? "restr GUIL2">] -> (i,f,b)
and restr_or_ax = parser
  | [< 'RESTRICT_KW >] -> true
  | [< 'AXIOM_KW >] -> false

(******************** LEMMA ********************)
and lem = parser
  | [< 'LEMMA_KW; 'IDENT l ?? "lem IDENT"; 'COLON ?? "lem COLON"; 
	t = tr_quant; 'GUIL ?? "lem GUIL1"; f = formula_; 
	'GUIL ?? "lem GUIL2">] -> (l,t,f)
and tr_quant = parser
  | [< 'ALLTR_KW >] -> AllTr
  | [< 'EXTR_KW >] -> ExTr
  | [< >] -> AllTr

(******************** FACTS ********************)
and facts_ = parser
  | [< lf = list0 fact_ com >] -> lf
and fact_ = parser
  | [< 'BANG; 'IDENT i ?? "fact_ IDENT"; s = suite_fact_ true i >] -> s
  | [< 'IDENT i; s = suite_fact_ false i >] -> s
and suite_fact_ b i = parser
  | [< 'LP; lm = list0 msetterm_ com; 
	'RP ?? "suite_fact_ RP">] -> (b,i,lm)

(******************** NODE ********************)
and node_ = parser
  | [< 'IDENT i; n = node_suit_ i>] -> n 
  | [< 'DIESE; 'IDENT i ?? "node_ IDENT1"; n = natural_ >] 
	-> (i,n,TimeNode)
  | [< 'DOLLAR; 'IDENT i ?? "node_ IDENT2"; n = natural_ >] 
	-> (i,n,PubNode)
  | [< 'TILD; 'IDENT i ?? "node IDENT3"; n = natural_ >] 
	-> (i,n,FreshNode)
and node_suit_ i = parser
  | [< 'DOTI n; _ = col; s = node_follow i (Some n) >] -> s
  | [< _ = col; s = node_follow i None >] -> s
and col = parser
  | [< 'COLON >] -> ()
  | [< >] -> ()
and node_follow i n = parser
  | [< 'PUB_KW >] -> (i,n,PubNode) 
  | [< 'NODE_KW >] -> (i,n,TimeNode)
  | [< 'FR_KW >] -> (i,n,FreshNode)
  | [< 'MSG_KW >] -> (i,n,MsgNode)
  | [< >] -> (i,n,MsgNode)

and literal = parser
  | [< 'TEXT t >] -> Id(t)
  | [< 'TEXTT t >] -> Fr(t)
  | [< n = node_ >] -> Node(n)
(*  | [< _; _ ?? "literal" >] -> Id("a") *)
  
(******************** FORMULA ********************)
and formula_ = parser
  | [< i1 = imp_; i2 = imp_aux_1 i1 >] -> i2
and imp_aux_1 i = parser
  | [< 'EQUIV; ii = imp_ >] -> (i,Some ii)
  | [< >] -> (i,None)
and imp_ = parser
  | [< d = disjonc_; i = imp_aux_2 d >] -> i
and imp_aux_2 d = parser 
  | [< 'IMPL; i = imp_ >] -> Imp_disj((d,i))
  | [< >] -> Imp(d)
and disjonc_ = parser
  | [< c = conjonc_; d = disjonc_aux c >] -> d
and disjonc_aux c = parser
  | [< 'OR; d = disjonc_ >] -> c :: d
  | [< >] -> [c]
and conjonc_ = parser
  | [< n = neg_; c = conjonc_aux n >] -> c
and conjonc_aux n = parser
  | [< 'AND; c = conjonc_ >] -> n :: c
  | [< >] -> [n]
and neg_ = parser
  | [< 'NOT; a = atom_ >] -> (true,a)
  | [< a = atom_ >] -> (false,a)
and atom_ = parser
  | [< 'TRUE >] -> T
  | [< 'FALSE >] -> F
  | [< 'LP; f = formula_; 'RP ?? "atom_ RP1" >] -> Nested(f)
  | [< 'LAST_KW; 'LP ?? "atom_ LP1"; n = node_; 'RP ?? "atom_ RP2" >] 
	-> Last(n)
  | [< 'IDENT i; s = suite_atom_ i >] -> s
  | [< q = quant_form; ll = some lvar; 'DOT ?? "atom_ DOT"; 
	f = formula_ >] -> Quantified(q,ll,f)
  | [< f = fact_; 'AT ?? "atom_ AT"; n = node_ >] -> Action(f,n)
  | [< n = node_; s = suite_node n >] -> s
  | [< m1 = msetterm_; 'EQUAL ?? "atom_ EQUAL"; 
	m2 = msetterm_ >] -> EqTerm(m1,m2)
and suite_atom_ i = parser
  | [< 'LP; s = suit i >] -> s
  | [< 'LB; t1 = tupleterm_; 'RB ?? "suite_atom_ RB"; t2 = term_; 
	'EQUAL ?? "suite_atom_ EQUAL"; m2 = msetterm_ >] 
	-> EqTerm([[[[Bin((i,t1,t2))]]]],m2)
  | [< n = node_suit_ i; s = suite_node n >] -> s 
  (*
  | [< s = suite_fact_ false i; 'AT; n = node_ >] -> Action(s,n)
  | [< s = suite_term_no_node i; 'EQUAL; m2 = msetterm_ >] -> EqTerm([[[[s]]]],m2) 
  *)
and suit i = parser
  | [< lm = list0 msetterm_ com; 'RP ?? "suit RP1"; 'AT ?? "suit AT"; 
	n = node_ >] -> Action((false,i,lm),n) 
  | [< mm = list0 multterm_ com; 'RP ?? "suit RP2"; 
	'EQUAL ?? "suit EQUAL"; m2 = msetterm_ >] -> EqTerm([[[[Nary((i,mm))]]]],m2) 
and suite_node n = parser
  | [< 'LEQ; n2 = node_ >] -> Ordering(n,n2)
  | [< 'EQUAL; n2 = node_ >] -> EqTemp(n,n2)
and lvar = parser
  | [< n = node_ >] -> NodeVar(n)
and quant_form = parser
  | [< 'EXFORM_KW >] -> ExForm
  | [< 'ALLFORM_KW >] -> AllForm

(******************** TERM ********************)
and tupleterm_ = parser
  | [< 'LEQ; m = l_msetterm_; 'GEQ ?? "tupleterm_ GEQ">] -> m
and l_msetterm_ = parser
  | [< m1 = msetterm_; m2 = l_msetterm_aux m1 >] -> m2
and l_msetterm_aux m = parser
  | [< 'COM; mm = l_msetterm_ >] -> m :: mm
  | [< >] -> [m]
and msetterm_ = parser
  | [< x1 = xorterm_; x2 = msetterm_aux x1 >] -> x2
and msetterm_aux x = parser
  | [< 'PLUS; xx = msetterm_ >] -> x :: xx
  | [< >] -> [x]
and xorterm_ = parser
  | [< m1 = multterm_; m2 = xorterm_aux m1 >] -> m2
and xorterm_aux m = parser
  | [< 'XOR; mm = xorterm_ >] -> m :: mm
  | [< >] -> [m]
and multterm_ = parser
  | [< e1 = expterm_; e2 = multterm_aux e1 >] -> e2
and multterm_aux e = parser
  | [< 'MUL; ee = multterm_ >] -> e :: ee
  | [< >] -> [e]
and expterm_ = parser
  | [< t1 = term_; t2 = expterm_aux t1 >] -> t2
and expterm_aux t = parser
  | [< 'EXP; tt = expterm_ >] -> t :: tt
  | [< >] -> [t]
and term_ = parser
  | [< t = tupleterm_ >] -> Tuple(t)
  | [< 'LP; m = msetterm_; 'RP ?? "term_ RP ">] -> Mse(m)
  | [< 'IDENT i; s = suite_term_ i >] -> s
  | [< l = literal >] -> Lit(l)
and suite_term_ i = parser
  | [< s = suite_term_no_node i >] -> s 
  | [< n = node_suit_ i >] -> Lit(Node(n))
and suite_term_no_node i = parser
  | [< 'LB; t1 = tupleterm_; 'RB ?? "suite_term_no_node RB "; t2 = term_ >] -> Bin((i,t1,t2)) (* binary_app *)
  | [< 'LP; mm = list0 multterm_ com; 'RP ?? "suite_term_no_node RP " >] -> Nary((i,mm)) (* nary_app *)
  
(******************** USED SEVERAL TIMES ********************)
and private_ = parser
  | [< 'PRIV_KW >] -> true 
  | [< >] -> false
and natural_ = parser
  | [< 'DOTI n >] -> Some n
  | [< >] -> None
and com = parser
  | [< 'COM >] -> ()

