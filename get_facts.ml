(*	In this file, we define the function that extracts from the AST 
	constructed from the source file (that is a tamarin protocol) all 
	the facts and strings (that is, between ' ') that appear in the 
	protocol.
*)

open ASD_tam;;
open String;;
open List;;
open Sys;;

let print_single e fas = 
  Printf.fprintf fas "\tString: %s\n" e
;;

let print_pair e fas = 
  let (i,n) = e in
  Printf.fprintf fas "\tAction label: %s, with arity %d\n" i n
;;

let rec add_list_pair l i n = 
  l := add_list_pair_aux !l i n
and add_list_pair_aux l i n = match l with
  | [] -> [(i,n)]
  | (s,k)::suit ->
      if (i = s)
      then l
      else (s,k)::(add_list_pair_aux suit i n)
;;

let rec add_list l i = 
  l := add_list_aux !l i
and add_list_aux l i = match l with
  | [] -> [i]
  | s::suit ->
      if (i = s)
      then l
      else s::(add_list_aux suit i)
;;

(*	Extracts all the facts and strings from an AST that follows the ASD 
	defined in the file ASD_tam.
*)
let rec get_fact_and_string th =
  let (i,bs) = th 
  and l_act = ref []
  and l_string = ref [] 
  in
  get_fact_and_string_aux l_act l_string bs;
  (!l_act,!l_string)
and get_fact_and_string_aux l_act l_string bs = match bs with
  | [] -> ()
  | b::suit -> 
      gfas_body l_act l_string b;
      get_fact_and_string_aux l_act l_string suit
and gfas_body l_act l_string b = match b with
  | Rule r -> gfas_rule l_act l_string r
  | _ -> ()
and gfas_rule l_act l_string r = 
  let (i,l,f1,f2,f3) = r in
(*
  if (((String.length i >= 2) &&
      (String.get i 0 = 'H') && 
      (String.get i 1 = '_')) ||
      (String.equal i "Setup"))
  then (get_from_human l_act l_string f2);
*)
  get_from_human l_act l_string f2;
  get_string l_string l f3
  
and get_from_human l_act l_string f = match f with
  | None -> ()
  | Some facts -> 
      get_fact l_act facts;
      get_string_human l_string facts

and get_string_human l_string facts = match facts with
  | [] -> ()
  | f::suit -> 
      let (_,_,m) = f in
      get_string_tupleterm l_string m;
      get_string_human l_string suit
  
and get_fact l_act facts = match facts with
  | [] -> ()
  | f::suit -> 
      let (_,i,m) = f in
      add_list_pair l_act i (List.length m);
      get_fact l_act suit

and get_string l_string let_b facts = match facts with
  | [] -> get_string_let l_string let_b
  | f::suit -> 
      get_string_aux l_string f;
      get_string l_string let_b suit

and get_string_aux l_string fact = 
  let (_,i,m) = fact in
  if (String.length i >= 3) 
  then (
    if ((String.sub i 0 3) = "Out")
    then get_string_tupleterm l_string m
  )

and get_string_let l_string let_b = match let_b with
  | [] -> ()
  | l::suit ->
      let (_,m) = l in
      get_string_msetterm l_string m;
      get_string_let l_string suit
      
and get_string_msetterm l_string m = match m with
  | [] -> ()
  | x::suit ->
      get_string_xorterm l_string x;
      get_string_msetterm l_string suit
and get_string_xorterm l_string x = match x with
  | [] -> ()
  | m::suit ->
      get_string_multterm l_string m;
      get_string_xorterm l_string suit
and get_string_multterm l_string m = match m with
  | [] -> ()
  | e::suit ->
      get_string_expterm l_string e;
      get_string_multterm l_string suit
and get_string_expterm l_string e = match e with
  | [] -> ()
  | t::suit ->
      get_string_term l_string t;
      get_string_expterm l_string suit
and get_string_term l_string t = match t with
  | Tuple tup -> get_string_tupleterm l_string tup
  | Mse mset -> get_string_msetterm l_string mset
  | Bin bin -> get_string_binary l_string bin
  | Nary nar -> get_string_nary l_string nar
  | Lit lit -> get_string_literal l_string lit
and get_string_tupleterm l_string t = match t with
  | [] -> ()
  | m::suit ->
      get_string_msetterm l_string m;
      get_string_tupleterm l_string suit
and get_string_binary l_string bin = 
  let (b,tuple,t) = bin in
  get_string_tupleterm l_string tuple;
  get_string_term l_string t;
and get_string_nary l_string nar = 
  let (n,x) = nar in
  get_string_xorterm l_string x
and get_string_literal l_string lit = match lit with
  | Id s -> add_list l_string s
  | Fr s -> add_list l_string s
  | _ -> () 
(*
and get_string_node l_string n = 
  let (i,_,_) = n in
  if (String.length i >=3) 
  then (
    if (String.get i 0 = (String.get "'" 0)) && 
       (String.get i (String.length i - 1) = (String.get "'" 0))
    then add_list l_string (String.sub i 1 (String.length i - 2))
  )
;;
*)
let rec map_list f l x = match l with
  | [] -> ()
  | a::suit -> f a x ; map_list f suit x
;;
  
let print_fact_and_string th fas = 
  let (l1,l2) = get_fact_and_string th in
  map_list print_pair l1 fas;
  Printf.fprintf fas "\n";
  map_list print_single l2 fas
;;



