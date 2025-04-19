parser grammar KeYParser;

import KeYGlobalDeclParser;
@ header
{

}
@ members
{}

options { tokenVocab = KeYLexer; } // use tokens from STLexer.g4

file
   : DOC_COMMENT* (profile? preferences? decls problem? proof?) EOF
   ;

problem
   : (PROBLEM LBRACE (t = termorseq) RBRACE | CHOOSECONTRACT (chooseContract = string_value SEMI)? | PROOFOBLIGATION (proofObligation = cvalue)? SEMI?) proofScript?
   ;

arrayopid
   : EMPTYBRACKETS LPAREN componentType = typemapping RPAREN
   ;

/**
 * In the special but important case of Taclets, we don't yet know
 * whether we are going to have a term or a formula, and it is hard
 * to decide a priori what we are looking at.  So the `term'
 * non-terminal will recognize a term or a formula.  The `formula'
 * reads a formula/term and throws an error if it wasn't a formula.
 * This gives a rather late error message. */
   //region terms and formulas
   
/*
weigl, 2021-03-12:
   It would be nice if the following left-recursion would work.
   ANTLR4 supports left-recursion, but their implementated resolution  of left-recursion
   does not resolve a working grammar, that adheres the term precedence of KeY.

   We are using the old grammar rules of the KeYParser.g (ANTLR3).
   Maybe someone with more understanding of ANTLR4 could solve the problem and
   write a more readable grammar.

term
:
    term (LGUILLEMETS labels = label RGUILLEMETS)   #termLabeled
  | term PARALLEL term        #parallel
  | MODALITY term             #termModality
  | locset_term               #termLocset
  | quantifierterm            #termQuantifier
  |	term STAR term            #termMult
  |<assoc=right> term (SLASH | PERCENT) term #termDivisionModulo
  | term (PLUS|MINUS) term    #termWeakArith
  | location_term             #termLocation
  | substitutionterm          #termSubstitution
  | term EQUALS term          #termEquals
  | term AND term             #conjunction_term
  | updateterm                #termUpdate
  | ifThenElseTerm            #termIfThenElse
  | ifExThenElseTerm          #termIfExThenElse
  | NOT term                  #negation
  | MINUS term                #unaryMinus
  | term OR term              #disjunction_term
  | term NOT_EQUALS term      #termNotEquals
  | term ( LESS | LESSEQUAL | GREATER |  GREATEREQUAL ) term #termCompare
  | term ASSIGN term          #elementary_update_term
  | term IMP term             #implication_term
  | term EQV term             #equivalence_term
  | LPAREN sort=sortId RPAREN term #cast
  | LPAREN term RPAREN        #termParen
  | AT name=simple_ident      #abbreviation
  | term LBRACKET target=term ASSIGN val=term  RBRACKET       #bracket_access_heap_upate
  | term LBRACKET id=simple_ident args=argument_list RBRACKET #bracket_access_heap_term
  | term LBRACKET STAR RBRACKET                               #bracket_access_star
  | term LBRACKET indexTerm=term (DOTRANGE rangeTo=term)? RBRACKET #bracket_access_indexrange
  | term DOT STAR             #dotAll
  | term argument_list        #termCall
  | term AT term              #termHeap
  | term DOT attrid           #termAttribute //this is ambigous
  | accessterm                #termAccess  //also handles function calls
  | literals                  #termLiterals
;
*/
   
   profile
   : PROFILE name = string_value SEMI
   ;

preferences
   : KEYSETTINGS (LBRACE s = string_value? RBRACE | c = cvalue) // LBRACE, RBRACE included in cvalue#table
   
   ;

proofScript
   : PROOFSCRIPT ps = STRING_LITERAL
   ;
   // PROOF
   
proof
   : PROOF EOF
   ;
   // Config
   
cfile
   : cvalue* EOF
   ;
   //csection: LBRACKET IDENT RBRACKET;
   
ckv
   : doc = DOC_COMMENT? ckey ':' cvalue
   ;

ckey
   : IDENT
   | STRING_LITERAL
   ;

cvalue
   : IDENT # csymbol
   | STRING_LITERAL # cstring
   | BIN_LITERAL # cintb
   | HEX_LITERAL # cinth
   | MINUS? INT_LITERAL # cintd
   | MINUS? FLOAT_LITERAL # cfpf
   | MINUS? DOUBLE_LITERAL # cfpd
   | MINUS? REAL_LITERAL # cfpr
   | (TRUE | FALSE) # cbool
   | LBRACE (ckv (COMMA ckv)*)? COMMA? RBRACE # table
   | LBRACKET (cvalue (COMMA cvalue)*)? COMMA? RBRACKET # list
   ;

