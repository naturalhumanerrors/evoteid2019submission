(*	In this file, we define the functions that allow to compare sets 
	of restrictions. *)

(* type_message = Common s -> tm, tmm
   type_message = Apos s -> 'pw', ...
*)
type type_message = 
  | Common of string 
  | Apos of string
;;

(* One("To","D")
   Three("Send",Common("tm"),"m")
*)
type type_fact = 
  | One of string * string
  | Three of string * type_message * string 
;;

type restriction_t = 
(* Learn() @k ==> From() @k *)
  | LF of type_message 
(* Receive() @k ==> From() @k *)
  | RF of type_message
(* Send() @k ==> To() @k *)
  | ST of type_message
(* Receive('type',message) @k & From() @k ==> Send('type', message) @i & To()@i & i < k *)
  | RS of type_message * type_message * bool 
(* Send('type',message) @k & To() @k ==> Receive('type', message) @i & From()@i & i < k *)
  | SR of type_message * type_message * bool 
(* Receive('type1',message1) @k & From() @k ==> Receive('type2', message2) @i & From()@i & i < k *)
  | RR of type_message * type_message
(* Send('type1',message1) @k & To() @k ==> Send('type2', message2) @i & To()@i & i < k *)
  | SS of type_message * type_message
;;

let translate restriction = 
  let l = "Learn"
  and s = "Send"
  and r = "Receive"
  and t = "To"
  and f = "From" in
  let (l1,l2,n) = match restriction with
  | LF tm -> ([Three(l,tm,"m")],[One(f,"S")],0)
  | RF tm -> ([Three(r,tm,"m")],[One(f,"S")],0)
  | ST tm -> ([Three(s,tm,"m")],[One(t,"S")],0)
  
  | RS (tm1,tm2,b) -> 
    if b 
    then ([Three(r,tm1,"m");One(f,"S")],
          [Three(s,tm2,"m");One(t,"S")],1)
    else ([Three(r,tm1,"m1");One(f,"S")],
          [Three(s,tm2,"m2");One(t,"S")],1)
  | SR (tm1,tm2,b) -> 
    if b 
    then ([Three(s,tm1,"m");One(t,"S")],
          [Three(r,tm2,"m");One(f,"S")],1)
    else ([Three(s,tm1,"m1");One(t,"S")],
          [Three(r,tm2,"m2");One(f,"S")],1)
  
  | RR (tm1,tm2) -> ([Three(r,tm1,"m1")],[Three(r,tm2,"m2")],0)
  | SS (tm1,tm2) -> ([Three(s,tm1,"m1")],[Three(s,tm2,"m2")],0)
  in
  (l1,l2,n)
;;

type set_restr = 
  | OneRestr of restriction_t
  | TwoRestr of restriction_t * restriction_t
  | ThreeRestr of restriction_t * restriction_t * restriction_t
;;

let get_r sr = match sr with
  | OneRestr r -> r
  | TwoRestr (r,_) -> r
  | ThreeRestr (r,_,_) -> r
;;

(*	This functions compares the set of traces allowed by two
	restrictions. If true, Traces(restr2) is included in
	Traces(restr1). *)
let rec compare restr1 restr2 = match (restr1,restr2) with
  | (LF tm1,LF tm2) -> compare_lf_rf_st tm1 tm2
  | (RF tm1,RF tm2) -> compare_lf_rf_st tm1 tm2
  | (ST tm1,ST tm2) -> compare_lf_rf_st tm1 tm2
  | (RS (tm1,tm2,b),RS (tm1',tm2',b')) -> 
      if (b && not b') || ((tm1 = tm2) && (tm1' <> tm2'))
      then false
      else ((compare_r_s tm1 tm1') && (compare_r_s tm2' tm2))
  | (SR (tm1,tm2,b),SR (tm1',tm2',b')) -> 
      if (b && not b') || ((tm1 = tm2) && (tm1' <> tm2'))
      then false
      else ((compare_r_s tm1 tm1') && (compare_r_s tm2' tm2))
  | (RR _,RR _) -> (restr1 = restr2)
  | (SS _,SS _) -> (restr1 = restr2)
  | _ -> false
and compare_lf_rf_st tm1 tm2 = match (tm1,tm2) with
  | (Apos _,Common _) -> true
  | _ -> (tm1 = tm2)
and compare_r_s tm1 tm1' = match (tm1,tm1') with
  | (Common _,Common _) -> true
  | (Apos _,Common _) -> true
  | (Apos x1,Apos x2) -> (x1 = x2)
  | _ -> false
;;

(*	This functions compares the set of traces allowed by two sets of 
	restrictions. If true, Traces(s2) is included in Traces(s1). 
	However, this is an under approximation, false does not mean not 
	inclusion. *)
let rec compare_set s1 s2 = match (s1,s2) with
	| (OneRestr(r1),OneRestr(ra)) -> compare r1 ra
	| (OneRestr _,TwoRestr(ra,rb)) -> 
		( (compare_set s1 (OneRestr(ra))) || 
		  (compare_set s1 (OneRestr(rb))) )
	| (OneRestr _,ThreeRestr(ra,rb,rc)) -> 
		( (compare_set s1 (OneRestr(ra))) || 
		  (compare_set s1 (OneRestr(rb))) || 
		  (compare_set s1 (OneRestr(rc))) )
	| (TwoRestr(r1,r2),_) -> 
		( (compare_set (OneRestr(r1)) s2) && 
		  (compare_set (OneRestr(r2)) s2) )
	| (ThreeRestr(r1,r2,r3),_) -> 
		( (compare_set (OneRestr(r1)) s2) && 
		  (compare_set (OneRestr(r2)) s2) &&
		  (compare_set (OneRestr(r3)) s2) )
;;
	
	
	
	
	

