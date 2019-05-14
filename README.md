To compile this project, Ocaml version 4.04.0 was used. However,
it is very possible that earlier version of OCaml can also work.

Then, one also need to write, in the file 'script.sh' the absolute path 
to Tamarin (PATH), Maude (MAUDE) and Graphviz (GRAPHVIZ).

The project is compiled by using the command 'make' (if you compile 
more than once, please use 'make clean' between usage of 'make'). Then,
the tool can be used by launching the command:
	./main.native file option
where file has to be the name of a folder in which there is a folder 
named 'Restriction' and a tamarin file named 'file.spthy'. If option is 
'only', then the file 'file.spthy' will be parsed and a file named 
Facts_and_strings is created where all the action label and strings 
appearing in that file are listed. If not, the whole procedure is 
launched to find a set of restriction(s) that ensures that every lemma 
is verified.

In that case, every restriction is stored in the file 
'All_restrictions_.spthy'. All the generated set of restriction(s) on 
which Tamarin will be launched can be found in the folder Restriction, 
where there will also be some files for the results of the different 
calls of Tamarin. The result is stored in the file 'WhichRestriction'.

For instance, to launch the tool on the simple voting protocol, use:
	./main.native SimpleProtocol compute
If you use it on with SimpleSelene, you won't get any result with option 
different from 'only', since Tamarin takes too much time to get a result 
on that file.

To change the strings that appear in the different restrictions, please 
take a look at the file 'generate_restrictions.ml', line 11-14. 
To change the kind of restrictions used, look in the same file, line 
151-184.

Finally, the lexer/parser is written so that any protocol valid in 
Tamarin can be dealt with (at least, with option equal to 'only'). 
It was written by using the syntax description in the Tamarin manual.
However, some features are not taken into account. Some keywords and 
the associated constructions cannot be used:
	-global_heuristic
	-formal_comment
	-modulo
	-rule_attrs
	-lemma_attrs
	-restriction_attrs
	-proof_skeleton
	-fact_annotes
	-diff

