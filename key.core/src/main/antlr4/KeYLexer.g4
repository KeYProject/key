lexer grammar KeYLexer;

@header {
    import java.util.HashMap;
    import java.util.LinkedHashMap;
}

@annotateclass{ @SuppressWarnings("all") } 

@members{
   private String modalityBegin = null;
   private String modalityEnd = null;

   private static HashMap<String,String> modNames = new LinkedHashMap<String,String>(20);
   private static HashMap<String,String> modPairs = new LinkedHashMap<String,String>(20);

   static {
      modNames.put("\\<","diamond");
      modNames.put("\\diamond","diamond");
      modNames.put("\\diamond_transaction","diamond_transaction");
      modNames.put("\\[","box");
      modNames.put("\\box","box");
      modNames.put("\\box_transaction","box_transaction");
      modNames.put("\\[[","throughout");
      modNames.put("\\throughout","throughout");
      modNames.put("\\throughout_transaction","throughout_transaction");

      modPairs.put("\\<","\\>");
      modPairs.put("\\[","\\]");

      //modPairs.put("\\[[","\\]]");

      modPairs.put("\\modality","\\endmodality");
      modPairs.put("\\diamond","\\endmodality");
      modPairs.put("\\diamond_transaction","\\endmodality");
      modPairs.put("\\box","\\endmodality");
      modPairs.put("\\box_transaction","\\endmodality");
      modPairs.put("\\throughout","\\endmodality");
      modPairs.put("\\throughout_transaction","\\endmodality");
   }

    private Token tokenBackStorage = null;
    @Override
    public void emit(Token token) {
       int MAX_K = 10;
       if (token.getType() == INT_LITERAL) {//rewrite INT_LITERALs to identifier when preceeded by an '('
           for (int k = 1; k <= MAX_K; k++) {
               int codePoint = _input.LA(k);
               if (Character.isWhitespace(codePoint)) continue;
               if (codePoint == '(') ((org.antlr.v4.runtime.CommonToken) token).setType(IDENT);
               break;
           }
       }
       if(token.getType() == PROOF) {
          tokenBackStorage = super.emitEOF();
          //will later be overwritten the EOF token
       }
       super.emit(token);
    }

    @Override
    public Token nextToken() {
        if(tokenBackStorage!=null) {
          Token t = tokenBackStorage;
          tokenBackStorage = null;
          return t;
        }
        return super.nextToken();
    }

}

tokens {MODALITY}

SORTS:'\\sorts';
GENERIC : '\\generic';
PROXY : '\\proxy';
EXTENDS : '\\extends';
ONEOF : '\\oneof';
ABSTRACT : '\\abstract';

// Keywords used in schema variable declarations
SCHEMAVARIABLES : '\\schemaVariables';
SCHEMAVAR : '\\schemaVar';
MODALOPERATOR : '\\modalOperator';
PROGRAM : '\\program';
FORMULA : '\\formula';
TERM : '\\term';
UPDATE : '\\update';
VARIABLES : '\\variables';
VARIABLE : '\\variable';
SKOLEMTERM : '\\skolemTerm';
SKOLEMFORMULA : '\\skolemFormula';
TERMLABEL : '\\termlabel';

// used in contracts
MODIFIES : '\\modifies';

// Keywords used in program variable declarations
PROGRAMVARIABLES : '\\programVariables';

// Keywords for varcond and related stuff
STORE_TERM_IN : '\\storeTermIn';
STORE_STMT_IN : '\\storeStmtIn';
HAS_INVARIANT : '\\hasInvariant';
GET_INVARIANT : '\\getInvariant';
GET_FREE_INVARIANT: '\\getFreeInvariant';
GET_VARIANT: '\\getVariant';
IS_LABELED: '\\isLabeled';

SAME_OBSERVER : '\\sameObserver';
VARCOND : '\\varcond';
APPLY_UPDATE_ON_RIGID : '\\applyUpdateOnRigid';
DEPENDINGON : '\\dependingOn';
DISJOINTMODULONULL  : '\\disjointModuloNull';
DROP_EFFECTLESS_ELEMENTARIES : '\\dropEffectlessElementaries';
DROP_EFFECTLESS_STORES : '\\dropEffectlessStores';
SIMPLIFY_IF_THEN_ELSE_UPDATE : '\\simplifyIfThenElseUpdate';
ENUM_CONST : '\\enumConstant';
FREELABELIN : '\\freeLabelIn';
HASSORT : '\\hasSort';
FIELDTYPE : '\\fieldType';
FINAL : '\\final';
ELEMSORT : '\\elemSort';
HASLABEL : '\\hasLabel';
HASSUBFORMULAS : '\\hasSubFormulas';
ISARRAY:'\\isArray';
ISARRAYLENGTH:'\\isArrayLength';
ISCONSTANT: '\\isConstant';
ISENUMTYPE:'\\isEnumType';
ISINDUCTVAR:'\\isInductVar';
ISLOCALVARIABLE : '\\isLocalVariable';
ISOBSERVER : '\\isObserver';
DIFFERENT : '\\different';
METADISJOINT : '\\metaDisjoint';
ISTHISREFERENCE:'\\isThisReference';
DIFFERENTFIELDS:'\\differentFields';
ISREFERENCE:'\\isReference';
ISREFERENCEARRAY:'\\isReferenceArray';
ISSTATICFIELD : '\\isStaticField';
ISMODELFIELD : '\\isModelField';
ISINSTRICTFP : '\\isInStrictFp';
ISSUBTYPE : '\\sub';
EQUAL_UNIQUE : '\\equalUnique';
NEW : '\\new';
NEW_TYPE_OF: '\\newTypeOf';
NEW_DEPENDING_ON: '\\newDependingOn';
HAS_ELEMENTARY_SORT:'\\hasElementarySort';
NEWLABEL : '\\newLabel';
CONTAINS_ASSIGNMENT : '\\containsAssignment';
// label occurs again for character `!'
NOT_ : '\\not';
NOTFREEIN : '\\notFreeIn';
SAME : '\\same';
STATIC : '\\static';
STATICMETHODREFERENCE : '\\staticMethodReference';
MAXEXPANDMETHOD : '\\mayExpandMethod';
STRICT    : '\\strict';
TYPEOF : '\\typeof';
INSTANTIATE_GENERIC : '\\instantiateGeneric';

// Quantifiers, binding, substitution
FORALL : '\\forall' | '\u2200';
EXISTS : '\\exists' | '\u2203';
SUBST  : '\\subst';
IF   : '\\if';
IFEX   : '\\ifEx';
THEN : '\\then';
ELSE : '\\else';

// inclusion and stuff, things that (usually) come at the beginning
// of the file
INCLUDE:'\\include';
INCLUDELDTS:'\\includeLDTs';
CLASSPATH:'\\classpath';
BOOTCLASSPATH:'\\bootclasspath';
NODEFAULTCLASSES:'\\noDefaultClasses';
JAVASOURCE:'\\javaSource';
WITHOPTIONS:'\\withOptions';
OPTIONSDECL:'\\optionsDecl';
KEYSETTINGS : '\\settings';
PROFILE : '\\profile';

// Those guys can stay being keywords
TRUE : 'true';
FALSE : 'false';

// Keywords related to taclets
SAMEUPDATELEVEL : '\\sameUpdateLevel';
INSEQUENTSTATE : '\\inSequentState';
ANTECEDENTPOLARITY : '\\antecedentPolarity';
SUCCEDENTPOLARITY : '\\succedentPolarity';
CLOSEGOAL : '\\closegoal';
HEURISTICSDECL : '\\heuristicsDecl';
NONINTERACTIVE : '\\noninteractive';
DISPLAYNAME : '\\displayname';
HELPTEXT : '\\helptext';
REPLACEWITH : '\\replacewith';
ADDRULES : '\\addrules';
ADDPROGVARS : '\\addprogvars';
HEURISTICS : '\\heuristics';
FIND : '\\find';
ADD : '\\add';
ASSUMES : '\\assumes';
TRIGGER : '\\trigger';
AVOID : '\\avoid';

PREDICATES : '\\predicates';
FUNCTIONS : '\\functions';
TRANSFORMERS : '\\transformers';
UNIQUE : '\\unique';

RULES : '\\rules';
AXIOMS : '\\axioms';
PROBLEM : '\\problem';
CHOOSECONTRACT : '\\chooseContract';
PROOFOBLIGATION : '\\proofObligation';
PROOF : '\\proof';
PROOFSCRIPT : '\\proofScript';
CONTRACTS : '\\contracts';
INVARIANTS : '\\invariants';

// Taclet annotations (see TacletAnnotations.java for more details)
LEMMA : '\\lemma';

// The first two guys are not really meta operators, treated separately
IN_TYPE : '\\inType';
IS_ABSTRACT_OR_INTERFACE : '\\isAbstractOrInterface';
CONTAINERTYPE : '\\containerType';

// types that need to be declared as keywords
//LOCSET : '\\locset';
//SEQ : '\\seq';
//BIGINT : '\\bigint';

// Unicode symbols for special functions/predicates
UTF_PRECEDES  : '\u227A' /*≺*/ | '\\precedes';
UTF_IN        : '\u220A' /*∊*/ | '\\in';
UTF_EMPTY     : '\u2205' /*∅*/ | '\\emptyset';
UTF_UNION     : '\u222A' /*∪*/ | '\\cup';
UTF_INTERSECT : '\u2229' /*∩*/ | '\\cap';
UTF_SUBSET_EQ : '\u2286' /*⊆*/ | '\\subseteq';
UTF_SUBSEQ    : '\u2282' /*⊂*/ | '\\subset';
UTF_SETMINUS  : '\u2216' /*∖*/ | '\\setminus';

fragment
VOCAB
   :       '\u0003'..'\u0377'
   ;

SEMI
:	';'
    ;

SLASH
:	'/'
    ;

COLON:    ':';

DOUBLECOLON
:    '::'
  ;

ASSIGN
:    ':='
    ;

DOT
:	'.'
	;

DOTRANGE
:	'.' '.'
	;

COMMA
:	','
	;

LPAREN
:
	'('
	;

RPAREN
:	')'
    ;

LBRACE
:	'{'
	;

RBRACE
:	'}'
    ;

LBRACKET
:	'['
    ;

RBRACKET
:	']'
	;

EMPTYBRACKETS
:	'[' ']'
	;

AT
:	'@'
	;

PARALLEL
:     '|' '|'
	;


OR
:	'|' | '\u2228'
	;

AND
:	'&' | '\u2227'
	;

NOT
:	'!' | '\u00AC'
	;

IMP
:	'->' | '\u2192'
	;

EQUALS
:	'='
	;

NOT_EQUALS
:	'!=' | '\u2260'
	;

SEQARROW
:	'==>' | '\u27F9'
	;

EXP
:	'^'
	;

TILDE
:	'~'
	;

PERCENT
:   '%'
      ;

STAR
:   '*'
      ;

MINUS
:   '-'
      ;

PLUS
:   '+'
      ;

GREATER
:   '>'
      ;

GREATEREQUAL
:   '>' '=' | '\u2265'
      ;

      
WS:  [ \t\n\r\u00a0]+ -> channel(HIDDEN); //U+00A0 = non breakable whitespace
STRING_LITERAL:'"' ('\\' . | ~( '"' | '\\') )* '"' ;
LESS: '<';
LESSEQUAL: '<' '=' | '\u2264';
LGUILLEMETS: '<' '<' | '«' | '‹';
RGUILLEMETS: '>''>' | '»' | '›';
IMPLICIT_IDENT: '<' (LETTER)+ '>' ('$lmtd')? -> type(IDENT);

EQV:	'<->' | '\u2194';
PRIMES:	('\'')+;
CHAR_LITERAL
: '\''
                ((' '..'&') |
                 ('('..'[') |
                 (']'..'~') |
                 ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"' | 'u' HEX ))
                )
      '\''
 ;

QUOTED_STRING_LITERAL
    : '"' ('\\' . | '\n' | ~('\n' | '"' | '\\') )* '"' ;

SL_COMMENT
:
	'//'
	(~('\n' | '\uFFFF'))* ('\n' | '\uFFFF' | EOF) -> channel(HIDDEN)
;

DOC_COMMENT: '/*!' -> more, pushMode(docComment);
ML_COMMENT: '/*' -> more, pushMode(COMMENT);


BIN_LITERAL: '0' 'b' ('0' | '1' | '_')+ ('l'|'L')?;

HEX_LITERAL: '0' 'x' (DIGIT | 'a'..'f' | 'A'..'F' | '_')+ ('l'|'L')?;
fragment DIGIT:	'0'..'9';
fragment HEX
:	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
    ;

fragment LETTER:	'a'..'z'|'A'..'Z';
fragment IDCHAR: LETTER | DIGIT | '_' | '#' | '$';


IDENT:  ( (LETTER | '_' | '#' | '$') (IDCHAR)*);

INT_LITERAL:
    (DIGIT | '_')+ ('l'|'L')?
;

fragment EXP_SUFFIX:
   ('e'|'E') ('+'|'-')? (DIGIT)+
   ;

// reals, floats and doubles are all rationals here.
fragment RATIONAL_LITERAL:
      (DIGIT)+ ('.' (DIGIT)*)? (EXP_SUFFIX)?
    | '.' (DIGIT)+ (EXP_SUFFIX)?
    ;

FLOAT_LITERAL:
    RATIONAL_LITERAL ('f' | 'F')
    ;

DOUBLE_LITERAL:
    RATIONAL_LITERAL ('d' | 'D')
    ;

REAL_LITERAL:
    RATIONAL_LITERAL ('r' | 'R')
    ;


/**
  * Here we have to accept all strings of ki01           ERROR_CHAR 0:\                                                 nd \\[a-z_]
  * and make the decision our selves as to what to do with it
  * (i.e. is it a modality, keyword, or possibly something else)
  */
MODALITYD:	'\\<' -> more, pushMode(modDiamond);
MODALITYB:	'\\[' -> more, pushMode(modBox);
MODALITYBB:	'\\[[' -> more, pushMode(modBoxBox);

MODAILITYGENERIC1: '\\box'                    -> more, pushMode(modGeneric);
MODAILITYGENERIC2: '\\diamond'                -> more, pushMode(modGeneric);
MODAILITYGENERIC3: '\\diamond_transaction'    -> more, pushMode(modGeneric);
MODAILITYGENERIC4: '\\modality'               -> more, pushMode(modGeneric);
MODAILITYGENERIC5: '\\box_transaction'        -> more, pushMode(modGeneric);
MODAILITYGENERIC6: '\\throughout'             -> more, pushMode(modGeneric);
MODAILITYGENERIC7: '\\throughout_transaction' -> more, pushMode(modGeneric);

/* weigl: not working
MODAILITYGENERIC:
      ('\\modality' | '\\diamond' | '\\diamond_transaction'
      '\\box' | '\\box_transaction' | '\\throughout' | '\\throughout_transaction')
      -> more, pushMode(modGeneric);
*/
//BACKSLASH:  '\\';
ESC_IDENT:  ( '\\' (LETTER | '_' | '#' | '$') (IDCHAR)*);
ERROR_CHAR: .;

mode modDiamond;
MODALITYD_END: '\\>' -> type(MODALITY), popMode;
MODALITYD_STRING : '"' -> more, pushMode(modString);
MODALITYD_CHAR : '\'' -> more, pushMode(modChar);
MODALITYD_COMMENT : [\\] [*] -> more, pushMode(modComment);
MODALITYD_ANY : . -> more;

mode modGeneric;
MODALITYG_END: '\\endmodality' -> type(MODALITY), popMode;
MODALITYG_STRING : '"' -> more, pushMode(modString);
MODALITYG_CHAR : '\'' -> more, pushMode(modChar);
MODALITYG_COMMENT : [\\] [*] -> more, pushMode(modComment);
MODALITYG_ANY : . -> more;

mode modBox;
MODALITYB_END: '\\]' -> type(MODALITY), popMode;
MODALITYB_STRING : '"' -> more, pushMode(modString);
MODALITYB_CHAR : '\'' -> more, pushMode(modChar);
MODALITYB_COMMENT : [\\] [*] -> more, pushMode(modComment);
MODALITYB_ANY : . -> more;

mode modBoxBox;
MODALITYBB_END: '\\]]' -> type(MODALITY), popMode;
MODALITYBB_STRING : '"' -> more, pushMode(modString);
MODALITYBB_CHAR : '\'' -> more, pushMode(modChar);
MODALITYBB_COMMENT : [\\] [*] -> more, pushMode(modComment);
MODALITYBB_ANY : . -> more;


mode modString;
MOD_STRING_ESC: [\\] '"' -> more;
MOD_STRING_END: '"' -> more,popMode;
MOD_STRING_ANY: . -> more;

mode modChar;
MOD_CHAR_END: '\'' -> more,popMode;
MOD_CHAR_ANY: . -> more;

mode modComment;
MOD_COMMENT_END: ('*/'|EOF) -> more, popMode;
MOD_COMMENT_ANY: . -> more;

mode COMMENT;
COMMENT_END: ('*/'|EOF) -> channel(HIDDEN), popMode;
COMMENT_ANY_CHAR: . -> more;

mode docComment;
DOC_COMMENT_END: ('*/'|EOF) -> type(DOC_COMMENT), popMode;
DOC_COMMENT_ANY_CHAR: . -> more;