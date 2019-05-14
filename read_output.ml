(*	In this file, we define the functions that allows to write 
	in a file. Moreover, we also defines a function to extract, from 
	an output produced by tamatin, what lemmas are verified and 
	which one are falsified.
*)

open Sys;;
(*
open String;;
*)
open Str;;
open Unix;;
open Generate_restrictions;;

let write_file name_file l =
  let f = open_out name_file in
  let rec write_rec l = match l with
    | [] -> () 
    | a::suite -> output_string f (a^"\n"); write_rec suite
  in 
  write_rec l;
  close_out f
;;

let rec get_steps l = match l with
	| a::b::suite when (b = "steps)") -> int_of_string (String.sub a 1 ((String.length a) -1))
	| a::suite -> get_steps suite
	| [] -> 0 

let rec what_falsified l = match l with
	| a::b::suite when a = "(exists-trace):" ->
		if (b = "falsified")
		then -1
		else 0
	| a::b::suite when a = "(all-traces):" ->
		if (b = "falsified")
		then (get_steps suite)
		else 1000 (* score for verifying a security lemma *) 
  | a::suite -> what_falsified suite
  | [] -> 0 
;;

(*	From an output produced by tamarin, this function extracts the 
	relevant informations and returns a score of type rslt that is 
	defined in the file generate_restrictions.ml.
*)
let rec what_output l d = match l with
  | [] -> TooLong d
  | a::suite when (a = "==============================================================================") -> 
	is_interesting suite true 0
  | _::suite -> what_output suite d
and is_interesting l sec_possible b = match l with
  | [] -> if (sec_possible) then OK else NoSecurity (0,b) 
  | a::suite ->
(*
      let l = String.split_on_char ' ' a in
*)
	  let l = Str.split (Str.regexp " ") a in
      let x = (what_falsified l) in
      if (x = -1) then NoFunctionnal 0
      else is_interesting suite (sec_possible && ((x = 0) || (x = 1000))) (b + x)
;;


let read_process_lines command =
  let lines = ref [] in
  let in_channel = Unix.open_process_in command in
  begin
    try
	  while true do
		let nextLine = input_line in_channel in
    	lines := nextLine :: !lines
	  done;
	with 
      End_of_file -> ignore (Unix.close_process_in in_channel)
  end;
  List.rev !lines
;;





