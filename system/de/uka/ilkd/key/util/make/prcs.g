// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
/* -*- java -*- */
//

header {
    package de.uka.ilkd.key.util.make;
    import java.io.*;
    import antlr.*;
}

// ######
// #     #    ##    #####    ####   ######  #####
// #     #   #  #   #    #  #       #       #    #
// ######   #    #  #    #   ####   #####   #    #
// #        ######  #####        #  #       #####
// #        #    #  #   #   #    #  #       #   #
// #        #    #  #    #   ####   ######  #    #


class ListJavaFiles extends Parser;
options {
	exportVocab=PRCS;
	k = 1;
}

{
    public static void main (String[] argv) {
        try {
            PRCSLexer lexer = new PRCSLexer(
                new BufferedReader(
                    new InputStreamReader(System.in)));
            ListJavaFiles parser = new ListJavaFiles(lexer);
            parser.project();
            System.out.print("\n");
        } catch(antlr.ANTLRException e) {
            System.err.println("Aborting due to Parse errors");
        }
    }

    private void handleFile(String f) {
        if ( f.endsWith(".java") && f.startsWith("system/de")) {
            System.out.print("\n"+f.substring(7,f.length()));
		}
    }
}


project: ( field )* ;

field: OPEN (files_fld | gibberish) CLOSE ;

files_fld : "Files" ( file_desc ) * ;

file_desc : OPEN file:WORD {handleFile(file.getText());}
            OPEN gibberish CLOSE flags CLOSE ;
gibberish : ( STRING | WORD  | OPEN gibberish CLOSE )* 
    ;

flags : ( FLAG ) *;

// #
// #        ######  #    #  ######  #####
// #        #        #  #   #       #    #
// #        #####     ##    #####   #    #
// #        #         ##    #       #####
// #        #        #  #   #       #   #
// #######  ######  #    #  ######  #    #


class PRCSLexer extends Lexer;
options {
	exportVocab=PRCS;
	k=2;
}

protected                                                                       
VOCAB                                                                           
        :       '\3'..'\377'                                                    
        ;                                                                       

OPEN : '(' ;
CLOSE : ')' ;

WS	
options {
  paraphrase = "white space";
}
	:	(' '
	|	'\t'
	|	'\n'  { newline(); }
	|	'\r')
		{ $setType(Token.SKIP); }
	;

STRING
options {
  paraphrase = "a string in double quotes";
}
    : '"'! ( ESC | ~('"'|'\\') )* '"'! ;

protected
ESC
    :	'\\'
    (	'n'         { $setText("\n"); } 
	|	'r' { $setText("\r"); }
	|	't' { $setText("\t"); }
	|	'b' { $setText("\b"); }
	|	'f' { $setText("\f"); }
	|	'"' { $setText("\""); }
	|	'\'' { $setText("'"); }
	|	'\\' { $setText("\\"); }
    )
    ;


SL_COMMENT 
options {
  paraphrase = "a comment";
}
	: ';'
	(~'\n')* '\n'
	{ $setType(Token.SKIP); newline(); }
	;

WORD 
    options {
    testLiterals = true;
    paraphrase = "a word";
}
:  ( WORDCHAR | ('\\' ( ' '| ')' | '(')) )+;

FLAG
options {
  paraphrase = "a flag";
}
: ':' WORD;

protected
WORDCHAR : ~(' '|'\f'|'\t'|'\n'|'\r'|')'|'('|';'|':'|'"') ;


