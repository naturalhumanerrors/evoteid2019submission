#!/bin/bash

PATH=~/.linuxbrew/Cellar/tamarin-prover/1.4.0/bin/tamarin-prover
MAUDE=~/.linuxbrew/Cellar/maude/2.7.1_1/bin/maude
GRAPHVIZ=~/.linuxbrew/Cellar/graphviz/2.40.1_1/bin/dot

if [ "$1" = "help" ]
then
	$PATH 
fi
if [ "$2" = "interactive" ]
then
	$PATH interactive $1 --with-maude=$MAUDE --with-dot=$GRAPHVIZ
fi
if [ "$2" = "prove" ]
then
	$PATH $1 --with-maude=$MAUDE --defines=$3 --prove 
fi
if [ "$2" = "parse" ]
then
	$PATH $1 --with-maude=$MAUDE --defines=$3 --parse-only
fi
