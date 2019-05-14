(*	In this file, we define the function that allows to have a 
	restriction written with the ASD defined in the file ASD_tam. 
	Therefore, it allows to use the pretty printer defined in that 
	same file to write these restrictions in a generated file.
*)

open ASD_tam;;
open List;;
open Compare_restriction;;

let rec add_list l_aux l i = 
  l := add_list_aux l_aux !l i
and add_list_aux l_aux l i = match (l_aux,l) with
  | ([],[]) -> [(i,MsgNode)]
  | ([],(s,t)::suit) ->
      if (i = s)
      then l
      else (s,t)::(add_list_aux l_aux suit i)
  | ((s,t)::suit,_) -> 
      if (i = s)
      then l
      else add_list_aux suit l i
;;

let rec pair_into_l_var e = 
  let (i,typenode) = e in
  NodeVar (i,None,typenode)
;;

let t_mset t = [[[[t]]]];;

let make_fact tf timestamp l_aux l_var = match tf with
  | One(name,identity) ->
      add_list l_aux l_var identity;
      let atom = 
        Action((false,
                name,
                [t_mset(Lit(Node(identity,None,MsgNode)))])
                ,(timestamp,None,MsgNode) ) (* could be TimeNode *)
      in
      atom
  | Three(name,tm,message) ->
      add_list l_aux l_var "H";
      add_list l_aux l_var message;
      let lit = ref (Lit(Id " ")) in
      (match tm with
        | Common s -> lit := Lit(Node (s,None,MsgNode)); add_list l_aux l_var s
        | Apos s -> lit := Lit(Id s)); 
  
      let atom = 
	  Action ((false,name,[t_mset(Lit(Node("H",None,MsgNode)));
						 t_mset(!lit);
						 t_mset(Lit(Node(message,None,MsgNode)))
					    ]
			   ),(timestamp,None,MsgNode) ) (* could be TimeNode *)
      in
      atom
;;			

let rec get_conj l timestamp l_aux l_var = match l with
  | [] -> []
  | a::suit ->
      let atom = make_fact a timestamp l_aux l_var in
      (false,atom) :: get_conj suit timestamp l_aux l_var
;;

let make_restriction l1 l2 n id = 
  let ts1 = ref "k" 
  and l_var1 = ref [("k",TimeNode)] 
  and ts2 = ref "j" 
  and l_var2 = ref [] 
  and ineq = ref []
  in
  (match n with
    | 0 -> ts2 := "k";
    | _ -> 
      l_var2 := [(!ts2,TimeNode)]; 
      ineq := [(false,Ordering((!ts2,None,MsgNode),(!ts1,None,MsgNode)))]); (* could be time nodes *)
    
  let name = "new_restriction_"^(string_of_int id)^"__" in
  let conj1 = get_conj l1 !ts1 [] l_var1 
  and conj2 = get_conj l2 !ts2 !l_var1 l_var2
  in
  let lv1 = List.map pair_into_l_var !l_var1
  and lv2 = List.map pair_into_l_var !l_var2
  in
  let right_form_without_quant = (Imp ([conj2]),None) in
  let right_imp = Imp ([[(false,Quantified (ExForm,lv2,right_form_without_quant))]]) in
  let form_without_quant = (Imp_disj ([conj1],right_imp),None) in
  let form = Quantified (AllForm,lv1,form_without_quant) in
  
  let f = (Imp([(false,form) :: !ineq]),None) in
  
  Restrict (name,f,true)
;;
