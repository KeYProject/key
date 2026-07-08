lexer grammar KeYLexer;

@ header
{
    import java.util.HashMap;
    import java.util.LinkedHashMap;
}
@ annotateclass
{ @SuppressWarnings("all") }
@ members
{
   private String modalityBegin = null;
   private String modalityEnd = null;

   private static HashMap<String,String> modNames = new LinkedHashMap<String,String>(20);
   private static HashMap<String,String> modPairs = new LinkedHashMap<String,String>(20);

   static {
      modNames.put("\\<","diamond");
      modNames.put("\\diamond","diamond");
      modNames.put("\\[","box");
      modNames.put("\\box","box");

      modPairs.put("\\modality","\\endmodality");
      modPairs.put("\\diamond","\\endmodality");
      modPairs.put("\\box","\\endmodality");

      modNames.put("\\diamond_transaction","diamond_transaction");
      modNames.put("\\box_transaction","box_transaction");
      modNames.put("\\[[","throughout");
      modNames.put("\\throughout","throughout");
      modNames.put("\\throughout_transaction","throughout_transaction");

      modPairs.put("\\diamond_transaction","\\endmodality");
      modPairs.put("\\box_transaction","\\endmodality");
      modPairs.put("\\throughout","\\endmodality");
      modPairs.put("\\throughout_transaction","\\endmodality");
   }

    private Token tokenBackStorage = null;
    @Override
    public void emit(Token token) {
       int MAX_K = 10;
       if (token.getType() == INT_LITERAL) {//rewrite INT_LITERALs to identifier when preceded by an '('
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

    /**
     * Called when, while scanning the body of a modality, another modality-opening keyword is
     * encountered. A modality body is a (schematic) program and must never contain a nested
     * modality, so this means the current modality's closing {@code \endmodality} (or {@code \>} /
     * {@code \]}) is missing. Fail the token at its start (the modality opening) -- mirroring the
     * behaviour at end-of-file -- so the error is reported there instead of running on to the next,
     * unrelated {@code \endmodality}. (See issue #3867.)
     */
    private void unterminatedModality() {
        throw new org.key_project.util.parsing.UnterminatedModalityException(
            "Missing '\\endmodality': this modality is not terminated (another modality opening "
                + "was found before its closing keyword).",
            _tokenStartLine, _tokenStartCharPositionInLine, getSourceName());
    }

}
tokens { MODALITY }
SORTS
   : '\\sorts'
   ;

GENERIC
   : '\\generic'
   ;

PROXY
   : '\\proxy'
   ;

EXTENDS
   : '\\extends'
   ;

ONEOF
   : '\\oneof'
   ;

ABSTRACT
   : '\\abstract'
   ;
ALIAS: '\\alias';

   // Keywords used in schema variable declarations
  
SCHEMAVARIABLES
   : '\\schemaVariables'
   ;

SCHEMAVAR
   : '\\schemaVar'
   ;

MODALOPERATOR
   : '\\modalOperator'
   ;

PROGRAM
   : '\\program'
   ;

FORMULA
   : '\\formula'
   ;

TERM
   : '\\term'
   ;

UPDATE
   : '\\update'
   ;

VARIABLES
   : '\\variables'
   ;

VARIABLE
   : '\\variable'
   ;

SKOLEMTERM
   : '\\skolemTerm'
   ;

SKOLEMFORMULA
   : '\\skolemFormula'
   ;
   
PROGRAMVARIABLES
   : '\\programVariables'
   ;

VARCOND
   : '\\varcond'
   ;

APPLY_UPDATE_ON_RIGID
   : '\\applyUpdateOnRigid'
   ;

DROP_EFFECTLESS_ELEMENTARIES
   : '\\dropEffectlessElementaries'
   ;

SIMPLIFY_IF_THEN_ELSE_UPDATE
   : '\\simplifyIfThenElseUpdate'
   ;

HASSORT
   : '\\hasSort'
   ;

ISINDUCTVAR
   : '\\isInductVar'
   ;

DIFFERENT
   : '\\different'
   ;

ISSUBTYPE
   : '\\sub'
   ;

EQUAL_UNIQUE
   : '\\equalUnique'
   ;

NEW
   : '\\new'
   ;

NEW_TYPE_OF
   : '\\newTypeOf'
   ;

HAS_ELEMENTARY_SORT
   : '\\hasElementarySort'
   ;
   // label occurs again for character `!'
   
NOT_
   : '\\not'
   ;

SAME
   : '\\same'
   ;

STRICT
   : '\\strict'
   ;

TYPEOF
   : '\\typeof'
   ;

INSTANTIATE_GENERIC
   : '\\instantiateGeneric'
   ;
   // Quantifiers, binding, substitution
   
FORALL
   : '\\forall'
   | '\u2200'
   ;

EXISTS
   : '\\exists'
   | '\u2203'
   ;

SUBST
   : '\\subst'
   ;

IF
   : '\\if'
   ;

IFEX
   : '\\ifEx'
   ;

THEN
   : '\\then'
   ;

ELSE
   : '\\else'
   ;
   // inclusion and stuff, things that (usually) come at the beginning
   
   // of the file
   
INCLUDE
   : '\\include'
   ;

INCLUDELDTS
   : '\\includeLDTs'
   ;

PROGRAMSOURCE
   : '\\programSource'
   ;

WITHOPTIONS
   : '\\withOptions'
   ;

OPTIONSDECL
   : '\\optionsDecl'
   ;

KEYSETTINGS
   : '\\settings'
   ;

PROFILE
   : '\\profile'
   ;
   // Those guys can stay being keywords
   
TRUE
   : 'true'
   ;

FALSE
   : 'false'
   ;
   // Keywords related to taclets
   
IGNOREUPDATELEVEL
   : '\\ignoreUpdateLevel'
   ;
   
INSEQUENTSTATE
   : '\\inSequentState'
   ;

ANTECEDENTPOLARITY
   : '\\antecedentPolarity'
   ;

SUCCEDENTPOLARITY
   : '\\succedentPolarity'
   ;

CLOSEGOAL
   : '\\closegoal'
   ;

HEURISTICSDECL
   : '\\heuristicsDecl'
   ;

NONINTERACTIVE
   : '\\noninteractive'
   ;

DISPLAYNAME
   : '\\displayname'
   ;

HELPTEXT
   : '\\helptext'
   ;

REPLACEWITH
   : '\\replacewith'
   ;

ADDRULES
   : '\\addrules'
   ;

ADDPROGVARS
   : '\\addprogvars'
   ;

HEURISTICS
   : '\\heuristics'
   ;

FIND
   : '\\find'
   ;

ADD
   : '\\add'
   ;

ASSUMES
   : '\\assumes'
   ;

TRIGGER
   : '\\trigger'
   ;

AVOID
   : '\\avoid'
   ;

PREDICATES
   : '\\predicates'
   ;

FUNCTIONS
   : '\\functions'
   ;

DATATYPES
   : '\\datatypes'
   ;

TRANSFORMERS
   : '\\transformers'
   ; // TODO: rename?
   
UNIQUE
   : '\\unique'
   ;

FREE
   : '\\free'
   ;

RULES
   : '\\rules'
   ;

AXIOMS
   : '\\axioms'
   ;

PROBLEM
   : '\\problem'
   ;

PROOFOBLIGATION
   : '\\proofObligation'
   ;

PROOF
   : '\\proof'
   ;

PROOFSCRIPT
   : '\\proofScript'
   ;
   // Taclet annotations (see TacletAnnotations.java for more details)
   
LEMMA
   : '\\lemma'
   ;
   // Unicode symbols for special functions/predicates
   
UTF_PRECEDES
   : '\u227A' /*≺*/
   
   | '\\precedes'
   ;

UTF_IN
   : '\u220A' /*∊*/
   
   | '\\in'
   ;

UTF_EMPTY
   : '\u2205' /*∅*/
   
   | '\\emptyset'
   ;

UTF_UNION
   : '\u222A' /*∪*/
   
   | '\\cup'
   ;

UTF_INTERSECT
   : '\u2229' /*∩*/
   
   | '\\cap'
   ;

UTF_SUBSET_EQ
   : '\u2286' /*⊆*/
   
   | '\\subseteq'
   ;

UTF_SUBSEQ
   : '\u2282' /*⊂*/
   
   | '\\subset'
   ;

UTF_SETMINUS
   : '\u2216' /*∖*/
   
   | '\\setminus'
   ;

fragment VOCAB
   : '\u0003' .. '\u0377'
   ;

SEMI
   : ';'
   ;

SLASH
   : '/'
   ;

COLON
   : ':'
   ;

DOUBLECOLON
   : '::'
   ;

ASSIGN
   : ':='
   ;

DOT
   : '.'
   ;

DOTRANGE
   : '.' '.'
   ;

COMMA
   : ','
   ;

LPAREN
   : '('
   ;

RPAREN
   : ')'
   ;

LBRACE
   : '{'
   ;

RBRACE
   : '}'
   ;

LBRACKET
   : '['
   ;

RBRACKET
   : ']'
   ;

EMPTYBRACKETS
   : '[' ']'
   ;

AT
   : '@'
   ;

PARALLEL
   : '|' '|'
   ;

OR
   : '|'
   | '\u2228'
   ;

AND
   : '&'
   | '\u2227'
   ;

NOT
   : '!'
   | '\u00AC'
   ;

IMP
   : '->'
   | '\u2192'
   ;

EQUALS
   : '='
   ;

NOT_EQUALS
   : '!='
   | '\u2260'
   ;

SEQARROW
   : '==>'
   | '\u27F9'
   ;

EXP
   : '^'
   ;

TILDE
   : '~'
   ;

PERCENT
   : '%'
   ;

STAR
   : '*'
   ;

MINUS
   : '-'
   ;

PLUS
   : '+'
   ;

GREATER
   : '>'
   ;

GREATEREQUAL
   : '>' '='
   | '\u2265'
   ;

OPENTYPEPARAMS : '<' '[';
CLOSETYPEPARAMS : ']' '>';

WS
   : [ \t\n\r\u00a0]+ -> channel (HIDDEN)
   ; //U+00A0 = non breakable whitespace
   
STRING_LITERAL
   : '"' ('\\' . | ~ ('"' | '\\'))* '"'
   ;

LESS
   : '<'
   ;

LESSEQUAL
   : '<' '='
   | '\u2264'
   ;

LGUILLEMETS
   : '<' '<'
   | '«'
   | '‹'
   ;

RGUILLEMETS
   : '>' '>'
   | '»'
   | '›'
   ;

EQV
   : '<->'
   | '\u2194'
   ;

PRIMES
   : ('\'')+
   ;

CHAR_LITERAL
   : '\'' ((' ' .. '&') | ('(' .. '[') | (']' .. '~') | ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"' | 'u' HEX))) '\''
   ;

QUOTED_STRING_LITERAL
   : '"' ('\\' . | '\n' | ~ ('\n' | '"' | '\\'))* '"'
   ;

SL_COMMENT
   : '//' (~ ('\n' | '\uFFFF'))* ('\n' | '\uFFFF' | EOF) -> channel (HIDDEN)
   ;

DOC_COMMENT
   : '/*!' -> more , pushMode (docComment)
   ;

ML_COMMENT
   : '/*' -> more , pushMode (COMMENT)
   ;

BIN_LITERAL
   : '0' 'b' ('0' | '1' | '_')+ ('l' | 'L')?
   ;

HEX_LITERAL
   : '0' 'x' (DIGIT | 'a' .. 'f' | 'A' .. 'F' | '_')+ ('l' | 'L')?
   ;

fragment DIGIT
   : '0' .. '9'
   ;

fragment HEX
   : ('a' .. 'f' | 'A' .. 'F' | DIGIT) ('a' .. 'f' | 'A' .. 'F' | DIGIT) ('a' .. 'f' | 'A' .. 'F' | DIGIT) ('a' .. 'f' | 'A' .. 'F' | DIGIT)
   ;

fragment LETTER
   : 'a' .. 'z'
   | 'A' .. 'Z'
   ;

fragment IDCHAR
   : LETTER
   | DIGIT
   | '_'
   | '#'
   | '$'
   ;

MATCH_IDENT: '?' IDENT?;

IDENT
   : ((LETTER | '_' | '#' | '$') (IDCHAR)*)
   ;

INT_LITERAL
   : (DIGIT | '_')+ ('l' | 'L')?
   ;

fragment EXP_SUFFIX
   : ('e' | 'E') ('+' | '-')? (DIGIT)+
   ;
   // reals, floats and doubles are all rationals here.
   
fragment RATIONAL_LITERAL
   : (DIGIT)+ ('.' (DIGIT)*)? (EXP_SUFFIX)?
   | '.' (DIGIT)+ (EXP_SUFFIX)?
   ;

FLOAT_LITERAL
   : RATIONAL_LITERAL ('f' | 'F')
   ;

DOUBLE_LITERAL
   : RATIONAL_LITERAL ('d' | 'D')
   ;

REAL_LITERAL
   : RATIONAL_LITERAL ('r' | 'R')?
   ;

/**
  * Here we have to accept all strings of ki01           ERROR_CHAR 0:\                                                 nd \\[a-z_]
  * and make the decision our selves as to what to do with it
  * (i.e. is it a modality, keyword, or possibly something else)
  */ MODALITYD
   : '\\<' -> more , pushMode (modDiamond)
   ;

MODALITYB
   : '\\[' -> more , pushMode (modBox)
   ;

MODAILITYGENERIC1
   : '\\box' -> more , pushMode (modGeneric)
   ;

MODAILITYGENERIC2
   : '\\diamond' -> more , pushMode (modGeneric)
   ;

MODAILITYGENERIC4
   : '\\modality' -> more , pushMode (modGeneric)
   ;

ERROR_UKNOWN_ESCAPE: '\\' IDENT;

ERROR_CHAR
   : .
   ;

/**
 * A modality-opening keyword. Inside a modality body (a schematic program) such a keyword can only
 * mean that the current modality was not terminated; see {@link #unterminatedModality}.
 */
fragment MODALITY_OPEN
   : '\\modality' | '\\diamond_transaction' | '\\box_transaction' | '\\diamond' | '\\box'
   | '\\throughout_transaction' | '\\throughout' | '\\<' | '\\[[' | '\\['
   ;

mode modDiamond;
MODALITYD_NESTED
   : MODALITY_OPEN { unterminatedModality (); } -> more
   ;

MODALITYD_END
   : '\\>' -> type (MODALITY) , popMode
   ;

MODALITYD_STRING
   : '"' -> more , pushMode (modString)
   ;

MODALITYD_CHAR
   : '\'' -> more , pushMode (modChar)
   ;

MODALITYD_COMMENT
   : [\\] [*] -> more , pushMode (modComment)
   ;

MODALITYD_LINE_COMMENT
   : '//' -> more , pushMode (modLineComment)
   ;

MODALITYD_BLOCK_COMMENT
   : '/*' -> more , pushMode (modComment)
   ;

MODALITYD_ANY
   : . -> more
   ;

mode modGeneric;
MODALITYG_END
   : '\\endmodality' -> type (MODALITY) , popMode
   ;

MODALITYG_NESTED
   : MODALITY_OPEN { unterminatedModality (); } -> more
   ;

MODALITYG_STRING
   : '"' -> more , pushMode (modString)
   ;

MODALITYG_CHAR
   : '\'' -> more , pushMode (modChar)
   ;

MODALITYG_COMMENT
   : [\\] [*] -> more , pushMode (modComment)
   ;

MODALITYG_LINE_COMMENT
   : '//' -> more , pushMode (modLineComment)
   ;

MODALITYG_BLOCK_COMMENT
   : '/*' -> more , pushMode (modComment)
   ;

MODALITYG_ANY
   : . -> more
   ;

mode modBox;
MODALITYB_END
   : '\\]' -> type (MODALITY) , popMode
   ;

MODALITYB_NESTED
   : MODALITY_OPEN { unterminatedModality (); } -> more
   ;

MODALITYB_STRING
   : '"' -> more , pushMode (modString)
   ;

MODALITYB_CHAR
   : '\'' -> more , pushMode (modChar)
   ;

MODALITYB_COMMENT
   : [\\] [*] -> more , pushMode (modComment)
   ;

MODALITYB_LINE_COMMENT
   : '//' -> more , pushMode (modLineComment)
   ;

MODALITYB_BLOCK_COMMENT
   : '/*' -> more , pushMode (modComment)
   ;

MODALITYB_ANY
   : . -> more
   ;

mode modBoxBox;
MODALITYBB_END
   : '\\]]' -> type (MODALITY) , popMode
   ;

MODALITYBB_STRING
   : '"' -> more , pushMode (modString)
   ;

MODALITYBB_CHAR
   : '\'' -> more , pushMode (modChar)
   ;

MODALITYBB_COMMENT
   : [\\] [*] -> more , pushMode (modComment)
   ;

MODALITYBB_ANY
   : . -> more
   ;

mode modString;
MOD_STRING_ESC
   : [\\] '"' -> more
   ;

MOD_STRING_END
   : '"' -> more , popMode
   ;

MOD_STRING_ANY
   : . -> more
   ;

mode modChar;
MOD_CHAR_END
   : '\'' -> more , popMode
   ;

MOD_CHAR_ANY
   : . -> more
   ;

mode modComment;
MOD_COMMENT_END
   : ('*/' | EOF) -> more , popMode
   ;

MOD_COMMENT_ANY
   : . -> more
   ;

// Java line comment inside a modality body: consume up to (and including) the end of line so that
// a modality opening/closing keyword in the comment is not mistaken for real syntax.
mode modLineComment;
MOD_LINE_COMMENT_END
   : ('\n' | EOF) -> more , popMode
   ;

MOD_LINE_COMMENT_ANY
   : . -> more
   ;

mode COMMENT;
COMMENT_END
   : ('*/' | EOF) -> channel (HIDDEN) , popMode
   ;

COMMENT_ANY_CHAR
   : . -> more
   ;

mode docComment;
DOC_COMMENT_END
   : ('*/' | EOF) -> type (DOC_COMMENT) , popMode
   ;

DOC_COMMENT_ANY_CHAR
   : . -> more
   ;

