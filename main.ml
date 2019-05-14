open Lexer_tam;;
open Parser_tam;;
open ASD_tam;;
open Get_facts;;
open Write_restrictions;;
open Generate_restrictions;;
open Read_output;;
open Compare_restriction;;
open Course_graph;;

open Sys;;
open Array;;
open Unix;;
open Random;;

let duration_without_restr = 60.;;

let () = 	
	let obj = argv.(1) 
	and only_fact_and_string = argv.(2) 
	in
	let f = obj^"/" in
	let path = f^obj^".spthy" 
	and final = f^"WhichRestriction"
	in
	let lexbuf = Lexing.from_channel (open_in path) in 
	try
		let token_stream = (Stream.of_list (Lexer_tam.tokenize lexbuf)) in 
		let ast = Parser_tam.protocol token_stream in
		
		let fas = open_out (f^"Facts_and_strings") in
		print_fact_and_string ast fas;
		close_out fas;
		
		if (only_fact_and_string <> "only")
		then
			(let final_res = open_out final in
			(* Try without any restriction *)
			let pref = "timeout --preserve-status "^(string_of_float duration_without_restr) in
			let res = read_process_lines (pref^" ./script.sh "^path^" prove untrained 2> /dev/null") in
			write_file (f^"result_without_restr") res;
			
			let test =
			(match (what_output res duration_without_restr) with
				| OK -> (	Printf.printf "\nSucces without restriction! Computed! \n\n";
							flush Pervasives.stdout;
							Printf.fprintf final_res "\nSucces without restriction! Computed! \n\n";
							true)
				| TooLong d -> 
					Printf.printf "\nComputation too long (%f s) without restrictions \n\n" duration_without_restr;
					flush Pervasives.stdout;
					Printf.fprintf final_res "\nComputation too long (%f s) without restrictions \n\n" duration_without_restr;
					false
				| _ -> 
					Printf.printf "\nNo succes without restriction! Computed! \n\n";
					flush Pervasives.stdout;
					Printf.fprintf final_res "\nNo succes without restriction! Computed! \n\n";
					false)
			in
			if not test
			then		
			let (a,t) = write_and_design f ast in 
			
			course t a final_res f;
			close_out final_res
			)
	with
		|Lexer_tam.Unexpected_character e ->
			begin
			Printf.printf "Unexpected character: `%c' at position '%d' on line '%d'\n"
				e.character e.pos e.line;
				exit 1 
			end
		| Stream.Error s ->
			begin
				print_string "mistake \n";
				print_string s;
				print_newline ();
				exit 1
			end		
;;
