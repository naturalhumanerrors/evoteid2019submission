(*	In this file, we define the function that goes throw the set of 
	restrictions to find a set that ensures every lemma and that is 
	as simple as possible. The main function is 'course'.
*)

open Array;;
open Sys;;
open Unix;;
open Random;;
open List;;
open Scanf;;

open Read_output;;
open Generate_restrictions;;
open Compare_restriction;;

exception Found of int;;
exception NotFound;;

let rec get_index a restr = 
	try 
		let n = Array.length a in
		for i = 0 to  n-1 do
			if ((Array.get a i).rstr = OneRestr(restr))
			then raise (Found (Array.get a i).index)
		done;
		raise NotFound
	with 
		| Found n -> n
		| NotFound -> -1
;;

let display_restr a id = match (Array.get a id).rstr with
	| OneRestr r -> 
		let n = string_of_int (get_index a r) in "Restriction ("^n^")" 
	| TwoRestr (r1,r2) -> 
		let n1 = string_of_int (get_index a r1) 
		and n2 = string_of_int (get_index a r2)
		in "Restriction ("^n1^","^n2^")" 
	| ThreeRestr (r1,r2,r3) -> 
		let n1 = string_of_int (get_index a r1) 
		and n2 = string_of_int (get_index a r2)
		and n3 = string_of_int (get_index a r3)
		in "Restriction ("^n1^","^n2^","^n3^")"
;;


exception TimesUp;;

let exec_command c duration = 
	let times_up _	= raise TimesUp in 
	Sys.set_signal sigalrm (Signal_handle times_up);
	
	let t = ITIMER_REAL in
	let s = { it_interval = 0.; it_value = duration } in
	ignore (setitimer t s);
	try
		let r = read_process_lines c in r
	with 
		TimesUp -> ["Aborted for duration "^(string_of_float duration)^" sec.\n"] 
;; 

let exec f id duration = 
	let dest_result = f^"Restriction/Result_"^(string_of_int id) 
	and file = f^"Restriction/Restriction_"^(string_of_int id) 
	and pref = "timeout --preserve-status "^(string_of_float duration)
	in
	let res = read_process_lines (pref^" ./script.sh "^(file)^".spthy prove untrained 2> /dev/null") in
	write_file (dest_result) res;
	what_output res duration
;;
	
let write_res t f_res id b d = 
	let s1 = display_restr t id 
	in
	if b
	then
		(let s = Printf.sprintf "Finished for set of restriction(s) %d!\n" id in
		Printf.printf (Scanf.format_from_string (s^"This is: "^s1^"\n\n") "");
		flush Pervasives.stdout;
		Printf.fprintf f_res (Scanf.format_from_string (s^"This is: "^s1^"\n\n") "");
		flush f_res)
	else
		(let s = Printf.sprintf "Finished for set of restriction(s) %d! Aborted for duration %f sec.\n" id d in
		Printf.printf (Scanf.format_from_string (s^"This is: "^s1^"\n\n") "");
		flush Pervasives.stdout;
		Printf.fprintf f_res (Scanf.format_from_string (s^"This is: "^s1^"\n\n") "");
		flush f_res)
;;

let write_nc t f_res id b origine = 
	let s1 = display_restr t id 
	and s2 = display_restr t origine
	in
	if b
	then
		(let s = Printf.sprintf "Set of restriction(s) %d not computed. No security from %d\n" id origine in
		Printf.printf (Scanf.format_from_string (s^"They are: "^s1^" and "^s2^"\n\n") "");
		flush Pervasives.stdout;
		Printf.fprintf f_res (Scanf.format_from_string (s^"They are: "^s1^" and "^s2^"\n\n") "");
		flush f_res)
	else
		(let s = Printf.sprintf "Set of restriction(s) %d not computed. No functionnality from %d\n" id origine in
		Printf.printf (Scanf.format_from_string (s^"They are: "^s1^" and "^s2^"\n\n") "");
		flush Pervasives.stdout;
		Printf.fprintf f_res (Scanf.format_from_string (s^"They are: "^s1^" and "^s2^"\n\n") "");
		flush f_res)
;;

let rec count_available l t = 
	let rec aux n l = match l with
		| [] -> n
		| x :: suite -> 
			if (Array.get t x).visited
			then aux n suite
			else aux (n+1) suite
	in
	aux 0 l
and choose_next l t =
	let rec aux n z = match z with
		| [] -> -1
		| x :: suite -> 
			if (Array.get t x).visited
			then aux n suite
			else (if (n = 0) then x else aux (n-1) suite)
	in
	let k = count_available l t in
	if (k = 0) 
	then (-1)
	else let x = Random.int k in aux x l
;;

let rec add_elem n l = match l with
	| [] -> ([n],false)
	| a :: suite -> if (a=n) then (l,true) else let (j,b) = add_elem n suite in (a::j,b)
;;

(*	That function is called when the set of restrictions of number id 
	is found not to ensure a functionnality lemma (that is, with 
	"exists-trace"). In that case, every set of restriction that allows 
	less traces that the one of number id has a score set to 
	NoFunctionnal id.
*)
let rec no_func id t f_res = 
	write_nc t f_res id false id;
	let z = Array.get t id in
	let rec aux origine l = match l with
		| [] -> ()
		| n :: suite -> 
			let x = Array.get t n in
			if not (x.visited)
			then (	x.visited <- true; 
					x.score <- Some (NoFunctionnal origine); 
					write_nc t f_res n false origine);
			aux origine suite
	in
	aux id (z.less_traces)
(*	That function is called when the set of restrictions of number id 
	is found not to ensure a security lemma (that is, with 
	"all-traces"). In that case, every set of restriction that allows 
	more traces that the one of number id has a score set to 
	NoSecurity (id,s) where s is the score (defined in file 
	read_output.ml)	of the set of number id.
*)
and no_sec id t f_res s = 
	write_nc t f_res id true id;
	let z = Array.get t id in
	let rec aux origine l = match l with
		| [] -> ()
		| n :: suite -> 
			let x = Array.get t n in
			if not (x.visited)
			then (	x.visited <- true; 
					x.score <- Some (NoSecurity (origine,s));
					write_nc t f_res n true origine);
			aux origine suite
	in
	aux id (z.more_traces)
;;

let array_into_list a = 
	let l = ref []
	and n = Array.length a 
	in
	for i = 0 to n-1 do
		l := i :: !l
	done;
	!l
;;

let empile n l = 
	l := n :: !l
;;

let other_choose_next l t =
	let rec aux z h = match z with
		| [] -> h
		| x :: suite -> 
			if (Array.get t x).visited
			then aux suite h
			else aux suite (x::h)
	in
	aux l []
;;

let remove x l = 
	let rec aux x k = match k with
		| [] -> failwith "List too lengthy"
		| a :: suite -> if (x = 0) then (suite,a) else let (s,b) = aux (x-1) suite in (a::s,b)
	in
	let (u,o) = aux x !l in
	l := u; o
;;

(*	Selects and remove randomly an elements from the list l. *)
let depile l = 
	let n = List.length !l in
	if (n = 0)
	then failwith "The pile is empty!"
	else let x = Random.int n in
	remove x l
;;

(*	Selects and remove randomly the head of the list l. *)
let true_depile l = 
	remove 0 l
;;

(* 	This function is called once every set of one restrictions has been 
	tested but not one has succeeded. It selects the set that is the 
	most promising: a set for which it took too much time to compute,
	or, if there is not any, a set that has best score.
*)

let best_result l = 
	let best_score = ref 0 
	and best_id = ref (-1)
	in
	let rec aux m i = match m with
		| [] -> ()
		| (a,b)::suite -> 
			(match b with
				| None -> ()
				| Some r ->	
					(match r with
						| NoSecurity (_,d) -> 
							if (d > !best_score)
							then (best_score := d; best_id := i)
						| TooLong _ -> 
							best_score := 10000; 
							best_id := i
						| _ -> ())); 
			aux suite (i+1)
	in
	aux l 0;
	(!best_id,!best_score)
;;	
	
let display_result t f_res = 
	let dis = "Sum up of every set of restrictions computed:\n" in 
	Printf.printf (Scanf.format_from_string dis "");
	flush Pervasives.stdout;
	Printf.fprintf f_res (Scanf.format_from_string dis "");
	let k = Array.length t in
	for i = 0 to k-1 do
		let x = (Array.get t i) in
		if x.visited
		then 
		let s = 
		match x.score with
			| Some r -> 
				(match r with
					| OK -> "Every lemma is verified!\n"
					| TooLong d -> "Computation took more than"^(string_of_float d)^" s\n"
					| NoFunctionnal i -> "The functionnality lemma was not verified by set "^(string_of_int i)^" \n"
					| NoSecurity (i,s) -> "The security lemma was not verified by set "^(string_of_int i)^" with score "^(string_of_int s)^"\n")
			| _ -> "No Score\n"
		in
		let display = "Set of restrictions number "^(string_of_int i)^": "^s in
		Printf.printf (Scanf.format_from_string display "");
		flush Pervasives.stdout;
		Printf.fprintf f_res (Scanf.format_from_string display "");
		flush f_res
	done
;;

let too_long_not_visited t = 
	let k = Array.length t in
	for i = 0 to k - 1 do
		let x = Array.get t i in
		match x.score with
			| Some r -> 
				(match r with 
					| TooLong _ -> x.visited <- false
					| _ -> () )
			| _ -> ()
	done
;;

let intersect_list l1 l2 = 
	let in_l a = List.mem a l2 in
	List.filter in_l l1
;;

let rec display_list l = match l with
	| [] -> print_newline()
	| a::suite -> print_int a; print_newline (); display_list suite
;;

(* 	That is the main function of the whole program.
	First, every set of one restriction is tested (stored in l, and then 
	in origin). If none of them ensures every lemmas, then the most 
	promising ones are chosen with the function best_result. Then,
	The set of restrictions is searched among the list 'less_traces'
	of most promising set chosen previously. 
	
	Once a set of restrictions s that ensures every lemma is verified, 
	we search among the list s.more_traces for a set of restrictions 
	that still ensures that every lemma is verified but that contains 
	less restrictions.
	
	Whenever Tamarin is called on a file with a	set of restrictions, 
	if a functionnality lemma (that is, with "exists-trace") is not 
	ensured, that result is propagated among set of restrictions that 
	allows less traces. Conversely, if a security lemma 
	(that is, with "all-traces") is not ensured, that result is 
	propagated among set of restrictions that allows more traces.
*)
let course t l f_res f = 
	Random.init 0;
	
	let test = ref false 
	and best = ref 0 
	and current = ref 0
	in
	
	let l_res = ref [] in 
	
	let duration = ref 60. in
	
	let test_id id = 
		let x = Array.get t id in
		if not (x.visited)
		then 
			let r = exec f x.index !duration in
			(match r with
				| OK -> (test := true; write_res t f_res id true 0.; x.visited <- true; x.score <- Some r)
				| TooLong d -> (write_res t f_res id false d; x.visited <- true; x.score <- Some r)
				| NoFunctionnal _ -> 
(*
					write_res t f_res id true 0.; 
*)
					x.visited <- true; 
					x.score <- Some (NoFunctionnal id);
					no_func id t f_res
				| NoSecurity (_,s) -> 
					best := max !best s;
(*
					write_res t f_res id true 0.; 
*)
					x.visited <- true; 
					x.score <- Some (NoSecurity (id,s));
					no_sec id t f_res s); 
	in
	let nb_one_restr_int = 15
	and origin = ref l 
	in
	while (not (!test)) && (!origin <> []) do
		current := true_depile origin;
		test_id !current; 
		l_res := (!current,(Array.get t (!current)).score) :: !l_res
	done;
	
	if (not (!test))
	then (
		Printf.printf "No set of one restriction was enough to ensure that every lemma is verified.\nWe llok at the most promising ones:\n\n";
		flush Pervasives.stdout;
		Printf.fprintf f_res "No set of one restriction was enough to ensure that every lemma is verified.\nWe llok at the most promising ones:\n\n";
		flush f_res;
		
		duration := 60.;
		let l_to_try = ref [] 
		and i = ref 0 
		in
		while (!i < nb_one_restr_int) && (!l_res <> []) do
			let (optim,sc) = best_result !l_res in
			if (-1 < optim)
			then 
				(let (a,_) = remove optim l_res in
				Printf.printf "%d is interesting with score %d.\n" a sc;
				flush Pervasives.stdout;
				Printf.fprintf f_res "%d is interesting with score %d.\n" a sc;
				flush f_res;
				l_to_try := (Array.get t a).less_traces :: !l_to_try; 
				i := !i + 1)
			else 
				i := nb_one_restr_int
		done;
		Printf.printf "\n";
		flush Pervasives.stdout;
		Printf.fprintf f_res "\n";
		flush f_res;
		
		let pile = ref [] in
		let z_to_try = Array.of_list !l_to_try in
		let kz_to_try = Array.length z_to_try in
		for i = 0 to (kz_to_try -1) do
			for j = i+1 to (kz_to_try -1) do
				pile := intersect_list (Array.get z_to_try i) (Array.get z_to_try j) @ !pile
			done;
		done;
		
	
		while (not (!test)) && (!pile <> []) do
			current := depile pile;
			test_id (!current);
		done);
		
	(* That sums up the result for all set of restriction(s) computed *)
(*
	display_result t f_res;
*)

	if (!test)
	then 
		(	Printf.printf "!!!!!!!!!!!!!!!!!!!! Success for set of restriction(s) %d! !!!!!!!!!!!!!!!!!!!!\nSearch for a more smaller set of restriction(s)\n\n" !current;
			Printf.fprintf f_res "!!!!!!!!!!!!!!!!!!!! Success for set of restriction(s) %d! !!!!!!!!!!!!!!!!!!!!\nSearch for a more smaller set of restriction(s)\n\n" !current;
			
			let new_test id best id_best = 
			let score_restr x = match x.rstr with
				| OneRestr _ -> 1
				| TwoRestr _ -> 2
				| ThreeRestr _ -> 3
			in
			
			let x = Array.get t id in
			let sc = score_restr x in
			if (sc < !best)
			then
				if not (x.visited)
				then 
					let r = exec f x.index !duration in
					(match r with
						| OK ->  (best := sc; id_best := id; write_res t f_res id true 0.; x.visited <- true; x.score <- Some r)
						| TooLong d -> (write_res t f_res id false d; x.visited <- true; x.score <- Some r)
						| NoFunctionnal _ -> (no_func id t f_res; x.visited <- true; x.score <- Some r)
						| NoSecurity (_,s) -> (no_sec id t f_res s; x.visited <- true; x.score <- Some r))
				else 
					(match x.score with
						| None -> ()
						| Some p -> 
							(match p with
								| OK -> (best := sc; id_best := id)
								| _ -> ()))
			in
			let l = ref (Array.get t !current).more_traces 
			and best = ref 4 
			and best_id = ref !current
			in
			while (!best > 1) && (!l <> []) do
				current := true_depile l;
				new_test !current best best_id; 
			done;
			current := !best_id;
			Printf.printf "Set of restriction(s) %d ensures that every lemma is verified!\n" !current;
			Printf.fprintf f_res "Set of restriction(s) %d ensures that every lemma is verified!\n" !current)
	else 
		(	Printf.printf "No set of restriction(s) succeded! Best score is %d.\n" !best;
			Printf.fprintf f_res "No set of restriction(s) succeded! Best score is %d.\n" !best)
;;
