parser grammar KeYParser;

@header {
  import de.uka.ilkd.key.util.parsing.*;
}

@members {
private SyntaxErrorReporter errorReporter = new SyntaxErrorReporter(getClass());
public SyntaxErrorReporter getErrorReporter() { return errorReporter;}
}

options { tokenVocab=KeYLexer; } // use tokens from STLexer.g4

file: DOC_COMMENT* (profile? preferences? decls problem? proof?) EOF;

decls
:
    ( bootClassPath          // for problems
    | stlist=classPaths      // for problems
    | string=javaSource      // for problems
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

problem
:
  ( PROBLEM LBRACE ( t=termorseq ) RBRACE
  | CHOOSECONTRACT (chooseContract=string_value SEMI)?
  | PROOFOBLIGATION  (proofObligation=string_value SEMI)?
  )
  proofScript?
;



one_include_statement
:
    (INCLUDE | INCLUDELDTS)
    one_include (COMMA one_include)* SEMI
;

one_include 
:
    absfile=IDENT | relfile=string_value
;

options_choice
:
  WITHOPTIONS activated_choice (COMMA activated_choice)* SEMI
;

activated_choice
:
    cat=IDENT COLON choice_=IDENT
;

option_decls
:
    OPTIONSDECL LBRACE (choice SEMI)* RBRACE
;

choice
:
  maindoc+=DOC_COMMENT*
  category=IDENT
  (COLON LBRACE optionDecl (COMMA optionDecl)* RBRACE)?
;

optionDecl: doc+=DOC_COMMENT? choice_option+=IDENT;

sort_decls
:
 SORTS LBRACE (one_sort_decl)* RBRACE
;

one_sort_decl
:
  doc=DOC_COMMENT?
  (
     GENERIC  sortIds=simple_ident_dots_comma_list
        (ONEOF sortOneOf = oneof_sorts)?
        (EXTENDS sortExt = extends_sorts)? SEMI
    | PROXY  sortIds=simple_ident_dots_comma_list (EXTENDS sortExt=extends_sorts)? SEMI
    | ABSTRACT? sortIds=simple_ident_dots_comma_list (EXTENDS sortExt=extends_sorts)?  SEMI
  )
;

simple_ident_dots
:
  simple_ident (DOT simple_ident)*
;

simple_ident_dots_comma_list
:
  simple_ident_dots (COMMA simple_ident_dots)*
;


extends_sorts
:
    sortId (COMMA sortId)*
;

oneof_sorts
:
    LBRACE
    s = sortId (COMMA s = sortId) *
    RBRACE
;

keyjavatype
:
    type = simple_ident_dots (EMPTYBRACKETS)*
;

prog_var_decls
:
    PROGRAMVARIABLES
    LBRACE
    (
        kjt = keyjavatype
        var_names = simple_ident_comma_list
        SEMI
    )*
    RBRACE
;

//this rule produces a StringLiteral
string_literal: id=STRING_LITERAL;

//this rule produces a String
string_value: STRING_LITERAL;

simple_ident
:
    id=IDENT
;

simple_ident_comma_list
:
    id = simple_ident (COMMA id = simple_ident )*
;


schema_var_decls :
    SCHEMAVARIABLES LBRACE
    ( one_schema_var_decl SEMI)*
    RBRACE
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

schema_modifiers
    :
        LBRACKET
        opts = simple_ident_comma_list
        RBRACKET
       
    ;

one_schema_modal_op_decl
:
    (LPAREN sort = sortId RPAREN)?
    LBRACE ids = simple_ident_comma_list RBRACE id = simple_ident
;

pred_decl
:
  doc=DOC_COMMENT?
  pred_name = funcpred_name
  (whereToBind=where_to_bind)?
  argSorts=arg_sorts
  SEMI
;

pred_decls
:
  PREDICATES LBRACE (pred_decl)* RBRACE
;

func_decl
:
  doc=DOC_COMMENT?
  (UNIQUE)?
  retSort = sortId
  func_name = funcpred_name
	whereToBind=where_to_bind?
  argSorts = arg_sorts
  func_decl_syntax?
  SEMI
;

func_decl_syntax
:
SYNTAX
    ( MIXFIX_HOLE | OPERATOR | simple_ident | LPAREN | RPAREN )+
;

/**
\datatypes {
 \free List = Nil | Cons(any head, List tail);
}
*/
datatype_decls:
  DATATYPES LBRACE datatype_decl* RBRACE
;

datatype_decl:
  doc=DOC_COMMENT?
  // weigl: all datatypes are free!
  // FREE?
  name=simple_ident
  EQUALS
  datatype_constructor (OR datatype_constructor)*
  SEMI
;

datatype_constructor:
  name=simple_ident
  (
    LPAREN
    (argSort+=sortId argName+=simple_ident
     (COMMA argSort+=sortId argName+=simple_ident)*
    )?
    RPAREN
  )?
;

func_decls
    :
        FUNCTIONS
        LBRACE
        (
            func_decl
        ) *
        RBRACE
    ;


// like arg_sorts but admits also the keyword "\formula"
arg_sorts_or_formula
:
    ( LPAREN
      arg_sorts_or_formula_helper
      (COMMA arg_sorts_or_formula_helper)*
      RPAREN
    )?
;

arg_sorts_or_formula_helper
:
    sortId | FORMULA
;

transform_decl
:
    doc=DOC_COMMENT?
    (retSort = sortId
    | FORMULA
    )

    trans_name=funcpred_name
    argSorts=arg_sorts_or_formula
    SEMI
;


transform_decls:
    TRANSFORMERS LBRACE (transform_decl)* RBRACE
;

arrayopid:
        EMPTYBRACKETS LPAREN componentType=keyjavatype RPAREN
;

arg_sorts:
        (LPAREN sortId (COMMA sortId)* RPAREN)?
;

where_to_bind:
        LBRACE
        b+=(TRUE | FALSE)
        (COMMA b+=(TRUE | FALSE) )*
        RBRACE
        
   ;

ruleset_decls
:
  HEURISTICSDECL LBRACE  (doc+=DOC_COMMENT? id+=simple_ident SEMI)* RBRACE
;

sortId
:
    id=simple_ident_dots (EMPTYBRACKETS)*
;

id_declaration
:
  id=IDENT ( COLON s=sortId )?
;

funcpred_name
:
  (sortId DOUBLECOLON)? (name=simple_ident_dots|num=INT_LITERAL)
;


/**
 * In the special but important case of Taclets, we don't yet know
 * whether we are going to have a term or a formula, and it is hard
 * to decide a priori what we are looking at.  So the `term'
 * non-terminal will recognize a term or a formula.  The `formula'
 * reads a formula/term and throws an error if it wasn't a formula.
 * This gives a rather late error message. */

//region terms and formulas

termEOF: term EOF; // toplevel

boolean_literal: TRUE | FALSE;
literals:
    boolean_literal
  | char_literal
  | integer
  | floatnum
  | string_literal
  | emptyset
;

emptyset: UTF_EMPTY;
term:
  (literals | simple_ident | OPERATOR
  | EQUALS | NOT_EQUALS | TILDE | EXP | SEMI | COMMA
  | FORALL | EXISTS | SUBST | IF | IFEX | THEN | ELSE
  | COLON | DOUBLECOLON | AND | OR | NOT | IMP | DOT
  | MODALITY
  // special case need to handled recursively because RBRACE and RPAREN are part
  // of the FOLLOW set of term.
  | LPAREN term RPAREN
  | LBRACE term RBRACE
  )+
  ;

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

integer:
  (INT_LITERAL | HEX_LITERAL | BIN_LITERAL)
;

floatnum: // called floatnum because "float" collide with the Java language
    FLOAT_LITERAL  #floatLiteral
  | DOUBLE_LITERAL #doubleLiteral
  | REAL_LITERAL   #realLiteral
;

char_literal:
    CHAR_LITERAL;


varId: id=IDENT;
varIds: ids=simple_ident_comma_list;

triggers
:
  TRIGGER
  LBRACE id=simple_ident RBRACE
  t=term
    (AVOID avoidCond+=term
      (COMMA avoidCond+=term )*)?
  SEMI
;

taclet
:
  doc=DOC_COMMENT?
  (LEMMA)?
  name=IDENT (choices_=option_list)?
  LBRACE
  ( form=term
  |
    ( SCHEMAVAR one_schema_var_decl SEMI) *
    ( ASSUMES LPAREN ifSeq=seq RPAREN ) ?
    ( FIND LPAREN find=termorseq RPAREN
        (   SAMEUPDATELEVEL
          | INSEQUENTSTATE
          | ANTECEDENTPOLARITY
          | SUCCEDENTPOLARITY
        )*
    )?

    ( VARCOND LPAREN varexplist RPAREN )*
    goalspecs
    modifiers
  )
  RBRACE
;

modifiers
:
  ( rs = rulesets
  | NONINTERACTIVE
  | DISPLAYNAME dname=string_value
  | HELPTEXT htext=string_value
  | triggers
  ) *
;

seq: ant=semisequent SEQARROW suc=semisequent;

seqEOF: seq EOF;

termorseq
:
      head=term (COMMA s=seq | SEQARROW ss=semisequent) ?
    | SEQARROW ss=semisequent
;

semisequent
:
    /* empty */
  | head=term ( COMMA ss=semisequent) ?
;

varexplist : varexp (COMMA varexp)* ;

varexp
:
  negate=NOT_?
  varexpId
  (LBRACKET  parameter+=IDENT (COMMA parameter+=IDENT)* RBRACKET)?
  (LPAREN varexp_argument (COMMA varexp_argument)* RPAREN)?
;


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

goalspecs:
      CLOSEGOAL
    | goalspecwithoption (SEMI goalspecwithoption)*
;

goalspecwithoption
 :
    soc=option_list LBRACE goalspec RBRACE
  | goalspec
;

option
:
  cat=IDENT COLON value=IDENT
;

option_list
:
  LPAREN
    (option_expr (COMMA option_expr)*)
  RPAREN
;

option_expr
:
    option_expr AND option_expr #option_expr_and
  | option_expr OR option_expr  #option_expr_or
  | NOT option_expr             #option_expr_not
  | LPAREN option_expr RPAREN   #option_expr_paren
  | option                      #option_expr_prop
;

goalspec
:
  (name=string_value COLON)?
  ( rwObj=replacewith
    addSeq=add?
    addRList=addrules?
    addpv=addprogvar?
  | addSeq=add (addRList=addrules)?
  | addRList=addrules
  )
;

replacewith:  REPLACEWITH LPAREN o=termorseq RPAREN;
add:          ADD LPAREN s=seq RPAREN;
addrules:     ADDRULES LPAREN lor=tacletlist RPAREN;
addprogvar:   ADDPROGVARS LPAREN pvs=pvset RPAREN;
tacletlist:   taclet (COMMA taclet)*;

pvset: varId (COMMA varId)*;

rulesets:
  HEURISTICS LPAREN ruleset
  (COMMA ruleset) * RPAREN
;

ruleset: id=IDENT;

metaId:  id=simple_ident ;

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


one_bound_variable
:
  s=sortId? id=simple_ident
;


invariants
:
   INVARIANTS LPAREN selfVar=one_bound_variable
   RPAREN
   LBRACE
   (one_invariant)*
   RBRACE
;

one_contract
:
   contractName = simple_ident LBRACE
   (prog_var_decls)?
   fma=term MODIFIES modifiesClause=term
   RBRACE SEMI
;

one_invariant
:
     invName = simple_ident LBRACE
     fma=term
     (DISPLAYNAME displayName=string_value)?
     RBRACE SEMI
;

rulesOrAxioms:
    doc=DOC_COMMENT?
    (RULES|AXIOMS)
    (choices = option_list)?
    (LBRACE (s=taclet SEMI)* RBRACE)
;

bootClassPath
:
  BOOTCLASSPATH id=string_value SEMI
;

classPaths
:
  CLASSPATH s=string_value (COMMA s=string_value)* SEMI
;

javaSource: JAVASOURCE result=oneJavaSource SEMI;

oneJavaSource
:
  ( string_value
  | COLON
  )+ 
;

profile: PROFILE name=string_value SEMI;

preferences
:
	KEYSETTINGS (LBRACE s=string_value? RBRACE
	            |  c=cvalue ) // LBRACE, RBRACE included in cvalue#table
;

proofScript
:
  PROOFSCRIPT ps = STRING_LITERAL
;

// PROOF
proof: PROOF EOF;

// Config
cfile: cvalue* EOF;
//csection: LBRACKET IDENT RBRACKET;
ckv: doc=DOC_COMMENT? ckey ':' cvalue;
ckey: IDENT | STRING_LITERAL;
cvalue:
    IDENT #csymbol
  | STRING_LITERAL #cstring
  | BIN_LITERAL #cintb
  | HEX_LITERAL #cinth
  | MINUS? INT_LITERAL #cintd
  | MINUS? FLOAT_LITERAL #cfpf
  | MINUS? DOUBLE_LITERAL #cfpd
  | MINUS? REAL_LITERAL #cfpr
  | (TRUE|FALSE) #cbool
  | LBRACE
     (ckv (COMMA ckv)*)? COMMA?
    RBRACE #table
  | LBRACKET (cvalue (COMMA cvalue)*)? COMMA? RBRACKET #list;
