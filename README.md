## Requirements

- Linux
- Ocaml version 4.04.0 or newer (older versions could also work)
- tamarin-prover
- Maude
- Graphviz

## Setup

- Replace the absolute paths to the required tools (Tamarin, Maude and Graphviz) in the file 'script.sh'
- Add execution rights to the file 'script.sh': 'chmod +x script.sh'
- Compile using 'make' command (if you need to compile more than once, you need to use 'make clean' before using 'make')

## Usage

Run using './main.native [file] [option]', where:
- file: name of the folder containing tamarin specification file named 'file.spthy' and a folder named 'Restriction'
- option: 'only' or 'compute'. 
   - If option 'only' is specified, then the file 'file.spthy' will be parsed and a file named 'Facts_and_strings' will be created, containing all the action labels and strings appearing in the specification file. 
   - If option 'compute' is specified, then the whole procedure is launched to find a set of restriction(s) that ensures that every lemma is verified. In that case, every restriction is stored in the file 'All_restrictions_.spthy'. All the generated set of restriction(s) on which Tamarin will be launched can be found in the folder Restriction, where there will also be some files for the results of the different calls of Tamarin. The result is stored in the file 'WhichRestriction'.

### Example

./main.native SimpleProtocol compute

## Additional information

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

