parser grammar JavaKeYParser;
import KeYParser;

@header {
  import de.uka.ilkd.key.util.parsing.*;
}

@members {
private SyntaxErrorReporter errorReporter = new SyntaxErrorReporter(getClass());
public SyntaxErrorReporter getErrorReporter() { return errorReporter;}
public boolean allowMatchId = false; // used in proof script parsing
}

options { tokenVocab=JavaKeYLexer; } // use tokens from STLexer.g4

problem
   : (PROBLEM LBRACE (t = termorseq) RBRACE | CHOOSECONTRACT (chooseContract = string_value SEMI)? | PROOFOBLIGATION (proofObligation = cvalue)? SEMI?) proofScriptEntry?
   ;

decls
:
    ( bootClassPath          // for problems
    | stlist=classPaths      // for problems
    | string=programSource      // for problems
    | one_include_statement
    | options_choice
    | option_decls
    | sort_decls
    | prog_var_decls
    | schema_var_decls
    | pred_decls
    | func_decls
    | transform_decls
    | datatype_decls
    | ruleset_decls
    | contracts             // for problems
    | invariants            // for problems
    | rulesOrAxioms         // for problems
    )*
;

//TODO Split
one_schema_var_decl
:
     MODALOPERATOR one_schema_modal_op_decl
   | PROGRAM
      (schema_modifiers)?
      id = simple_ident
      (LBRACKET nameString=simple_ident EQUALS parameter=simple_ident_dots RBRACKET)?
      ids=simple_ident_comma_list
   | FORMULA
     (schema_modifiers)?
      ids = simple_ident_comma_list
   | TERMLABEL
     (schema_modifiers)?
     ids=simple_ident_comma_list
   | UPDATE
     (schema_modifiers)?
     ids=simple_ident_comma_list
   | SKOLEMFORMULA
     (schema_modifiers)?
     ids=simple_ident_comma_list
   | ( TERM
     | (VARIABLES | VARIABLE)
     | SKOLEMTERM
     )
     (schema_modifiers)?
     s=sortId
     ids=simple_ident_comma_list
;

arrayopid:
        EMPTYBRACKETS LPAREN componentType=typemapping RPAREN
;

/**
 * In the special but important case of Taclets, we don't yet know
 * whether we are going to have a term or a formula, and it is hard
 * to decide a priori what we are looking at.  So the `term'
 * non-terminal will recognize a term or a formula.  The `formula'
 * reads a formula/term and throws an error if it wasn't a formula.
 * This gives a rather late error message. */

//region terms and formulas

literals:
    boolean_literal
  | char_literal
  | integer
  | floatnum
  | string_literal
  | emptyset
//  | LPAREN {allowMatchId=true;} (term | seq) {allowMatchId=false;} RPAREN
;

//labeled_term: a=parallel_term (LGUILLEMETS labels=label RGUILLEMETS)?;

atom_prefix:
    update_term
  | substitution_term
  | locset_term
  | cast_term
  | unary_minus_term
  | bracket_term
;
bracket_term: primitive_labeled_term (bracket_suffix_heap)* attribute*;
bracket_suffix_heap: brace_suffix (AT heap=bracket_term)?;
brace_suffix:
    LBRACKET target=term ASSIGN val=term RBRACKET             #bracket_access_heap_update
  | LBRACKET id=simple_ident args=argument_list RBRACKET      #bracket_access_heap_term
  | LBRACKET STAR RBRACKET                                    #bracket_access_star
  | LBRACKET indexTerm=term (DOTRANGE rangeTo=term)? RBRACKET #bracket_access_indexrange
;
primitive_labeled_term:
  primitive_term ( LGUILLEMETS labels= label RGUILLEMETS )?;

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

attribute:
    DOT STAR                                                             #attribute_star
  | DOT id=simple_ident call? (AT heap=bracket_term)?                    #attribute_simple
  | DOT LPAREN sort=sortId DOUBLECOLON id=simple_ident RPAREN
     call? (AT heap=bracket_term)?                                       #attribute_complex
;

label
:
   l=single_label  (COMMA l=single_label )*
;

single_label
:
  (name=IDENT
  | star=STAR  )

  (LPAREN
    (string_value
      (COMMA string_value )*
    )?
    RPAREN
  )?
;

location_term
:
    LPAREN obj=equivalence_term COMMA field=equivalence_term RPAREN
;

locset_term
:
    LBRACE
        ( l = location_term 
        ( COMMA l = location_term  )* )?
    RBRACE
;

char_literal:
    CHAR_LITERAL;

varexpId: // weigl, 2021-03-12: This will be later just an arbitrary identifier. Only for backwards compatibility.
    APPLY_UPDATE_ON_RIGID
  | SAME_OBSERVER
  | DROP_EFFECTLESS_ELEMENTARIES
  | DROP_EFFECTLESS_STORES
  | DIFFERENTFIELDS
  | SIMPLIFY_IF_THEN_ELSE_UPDATE
  | CONTAINS_ASSIGNMENT
  | ISENUMTYPE
  | ISTHISREFERENCE
  | STATICMETHODREFERENCE
  | ISREFERENCEARRAY
  | ISARRAY
  | ISARRAYLENGTH
  | IS_ABSTRACT_OR_INTERFACE
  | IS_FINAL
  | ENUM_CONST
  | FINAL
  | STATIC
  | ISLOCALVARIABLE
  | ISOBSERVER
  | DIFFERENT
  | METADISJOINT
  | EQUAL_UNIQUE
  | FREELABELIN
  | ISCONSTANT
  | HASLABEL
  | ISSTATICFIELD
  | ISMODELFIELD
  | HASSUBFORMULAS
  | FIELDTYPE
  | NEW
  | NEW_TYPE_OF
  | NEW_DEPENDING_ON
  | NEW_LOCAL_VARS
  | HAS_ELEMENTARY_SORT
  | SAME
  | ISSUBTYPE
  | STRICT ISSUBTYPE
  | DISJOINTMODULONULL
  | NOTFREEIN
  | HASSORT
  | NEWLABEL
  | ISREFERENCE
  | MAXEXPANDMETHOD
  | STORE_TERM_IN
  | STORE_STMT_IN
  | HAS_INVARIANT
  | GET_INVARIANT
  | GET_FREE_INVARIANT
  | GET_VARIANT
  | IS_LABELED
  | ISINSTRICTFP
;

varexp_argument
:
    //weigl: Ambguity between term (which can also contain simple_ident_dots and sortId)
    //       suggestion add an explicit keyword to request the sort by name or manually resolve later in builder
    TYPEOF LPAREN y=varId RPAREN
  | CONTAINERTYPE LPAREN y=varId RPAREN
  | DEPENDINGON LPAREN y=varId RPAREN
  | term
;

metaTerm:
    vf=metaId (LPAREN t+=term (COMMA t+=term)* RPAREN)?
;

contracts
:
   CONTRACTS
   LBRACE
   (one_contract)*
   RBRACE
;

invariants
:
   INVARIANTS LPAREN selfVar=one_bound_variable RPAREN
   LBRACE
   (one_invariant)*
   RBRACE
;

one_contract
:
   contractName = simple_ident LBRACE
   (prog_var_decls)?
   fma=term MODIFIABLE modifiableClause=term
   RBRACE SEMI
;

one_invariant
:
     invName = simple_ident LBRACE
     fma=term
     (DISPLAYNAME displayName=string_value)?
     RBRACE SEMI
;

bootClassPath
:
  BOOTCLASSPATH id=string_value SEMI
;

classPaths
:
  CLASSPATH s=string_value (COMMA s=string_value)* SEMI
;

programSource: JAVASOURCE result=oneProgramSource SEMI;

simple_ident
   :
     id = IDENT
   | /*{allowMatchId}?*/ id=MATCH_IDENT
   ;

