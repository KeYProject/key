// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

lexer grammar KeYLexer;

//options {
//    k=2;
//}

/* -*-Antlr-*- */

@header {
    package de.uka.ilkd.key.parser;

    import java.io.InputStream;
    import de.uka.ilkd.key.util.*;
    import java.util.HashMap;
    import java.util.LinkedHashMap;
    import antlr.CharStreamException;
    import antlr.TokenStreamException;
    import org.antlr.runtime.*;
    import java.util.NoSuchElementException;
    import java.io.*;
}

@members{
    class SaveStruct {
        SaveStruct (CharStream input) {
            this.input = input;
            this.marker = input.mark();
        }

        public CharStream input;
        public int marker;
    }

    Stack<String> paraphrase = new Stack<String>();

    protected KeYExceptionHandler keh = new KeYRecoderExcHandler();
    protected Stack<SaveStruct> selector;

    // why is keh sometimes null?

    public KeYLexer(InputStream in, KeYExceptionHandler keh) throws IOException {
        this(new ANTLRInputStream(in));
	if(keh != null)
            this.keh = keh;
	this.selector = new Stack<SaveStruct>();
	//selector.select(this);
    }

    public KeYLexer(InputStream in, KeYExceptionHandler keh,
                    Stack<SaveStruct> selector) throws IOException {
        this(new ANTLRInputStream(in));
	if(keh != null)
          this.keh = keh;
	this.selector = selector;
    }

    public KeYLexer(Reader in, KeYExceptionHandler keh) throws IOException {
        this(new ANTLRReaderStream(in));
	if(keh != null)
          this.keh = keh;
	this.selector = new Stack<SaveStruct>();
	//selector.select(this);
    }

    public KeYLexer(CharStream in, KeYExceptionHandler keh) {
	this(in);
	if(keh != null) { this.keh = keh; }
	this.selector = new Stack<SaveStruct>();
    }

    public KeYLexer(String in, KeYExceptionHandler keh) {
	this(new ANTLRStringStream(in), keh);
    }

    public void reportError(RecognitionException ex){
        keh.reportException(ex);
    }

    public Stack<SaveStruct> getSelector() {
      return selector;
    }

   // We should override this method for handling EOF of included file
   @Override
   public Token nextToken(){
     Token token = super.nextToken();

     if (token.getType() == Token.EOF && !selector.empty()) {
       // We've got EOF and have non empty stack.
       SaveStruct ss = selector.pop();
       setCharStream(ss.input);
       input.rewind(ss.marker);
       // this should be used instead of super [like below] to handle exits from nested includes
       // it matters, when the 'include' token is the last in previous stream (using super, lexer 'crashes' returning EOF token)
       token = this.nextToken();
     }

     // Skip first token after switching on another input.
     // You need to use this rather than super as there may be nested include files
     if (((CommonToken)token).getStartIndex() < 0) {
       token = this.nextToken();
     }

     return token;
   }

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
      modPairs.put("\\modality","\\endmodality");
      modPairs.put("\\diamond","\\endmodality");
      modPairs.put("\\diamond_transaction","\\endmodality");
      modPairs.put("\\[","\\]");
      modPairs.put("\\box","\\endmodality");
      modPairs.put("\\box_transaction","\\endmodality");
      modPairs.put("\\[[","\\]]");
      modPairs.put("\\throughout","\\endmodality");
      modPairs.put("\\throughout_transaction","\\endmodality");
   }

   private void newline() {
     Debug.out("newline() was called but ANTLRv3 does not implement it anymore.");
   }

   public void recover( RecognitionException ex, BitSet tokenSet ) throws CharStreamException {
     input.consume();
     int ttype = input.LA(1);
     while (ttype != Token.EOF && !tokenSet.member(ttype)) {
       input.consume();
       ttype = input.LA(1);
     }
   }

   private void matchAndTransformModality(int beginIndex) throws RecognitionException {
      if(!modalityEnd.equals((String)modPairs.get(modalityBegin)))
          throw new NoViableAltException("Unknown modality " +
	   "expression "+modalityBegin+"..."+modalityEnd+". (" +
	     getSourceName() + ", " + getLine() + ", " + getCharPositionInLine() + ")", -1, -1, input);

      StringBuffer newText = new StringBuffer();
      int index = 0;
      int first = 0;
      int last = 0;
      String s = getText();
      newText.append(s.substring(0,beginIndex));
      index = beginIndex + modalityBegin.length();
      String modName = "";
      if("\\modality".equals(modalityBegin)) {
         // Have to extract the name of (schema) modality inside the first {}
	 while(s.charAt(index) == ' ' || s.charAt(index) == '\t' ||
	       s.charAt(index) == '\n' || s.charAt(index) == '\r') index++;
	 if(s.charAt(index) != '{') {
           throw new NoViableAltException("Expression "+modalityBegin+" should be followed by {...}. (" +
	     getSourceName() + ", " + getLine() + ", " + getCharPositionInLine() + ")", -1, -1, input);
	 }
         index++;
	 first = index;
	 char currChar = s.charAt(index);
	 while(currChar == ' ' || currChar == '\t' ||
	       currChar == '\r' || currChar == '\n') {
	     index++; first = index;
	     currChar = s.charAt(index);
	 }
	 last = first;
	 while((currChar >= 'a' && currChar <= 'z') ||
	        (currChar >= 'A' && currChar <= 'Z') ||
		currChar == '_' || currChar == '#') {
	     index++; last = index;
	     currChar = s.charAt(index);
	 }
	 while(currChar == ' ' || currChar == '\t' ||
	       currChar == '\r' || currChar == '\n') {
	     index++;
	     currChar = s.charAt(index);
	 }
	 if(s.charAt(index) != '}') {
            throw new NoViableAltException("Expected '}', found "+s.charAt(index)+". (" + getSourceName() + ", " + getLine() + ", " + getCharPositionInLine() + ")", -1, -1, input);
         }
	 index++;
	 modName=s.substring(first,last);
	 if("".equals(modName)) {
            throw new NoViableAltException("Empty modality name. Modality block	was: "+s + "(" + getSourceName() + ", " + getLine() + ", " + getCharPositionInLine() + ")", -1, -1, input);
	 }
      }else{
         modName = (String)modNames.get(modalityBegin);
	 if(modName==null) {
            throw new NoViableAltException("Unknown modality "+modalityBegin+". (" + getSourceName() + ", " + getLine() + ", " + getCharPositionInLine() + ")", -1, -1, input);
	 }

      }
      newText.append(modName+"\n");
      Debug.out("Modality name :", modName);
      last = s.lastIndexOf(modalityEnd);
      newText.append(s.substring(index,last));
      setText(newText.toString());
      Debug.out("Lexer: recognised Java block string: ", getText());
   }

}

/**
 * The common lexer for declarations, terms, formulae, Taclets, etc.
 */

        // Keywords used in sort declarations
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
	SKOLEMTERM : '\\skolemTerm';
	SKOLEMFORMULA : '\\skolemFormula';
	TERMLABEL : '\\termlabel';

        // used in contracts
	MODIFIES : '\\modifies';

        // Keywords used in program variable declarations
	PROGRAMVARIABLES : '\\programVariables';

        // Keywords for varcond and related stuff
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
	ISSUBTYPE : '\\sub';
	EQUAL_UNIQUE : '\\equalUnique';
        NEW : '\\new';
        NEWLABEL : '\\newLabel';
// label occurs again for character `!'
	NOT_ : '\\not';
        NOTFREEIN : '\\notFreeIn';
	SAME : '\\same';
	STATIC : '\\static';
        STATICMETHODREFERENCE : '\\staticMethodReference';
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
        PROBLEM : '\\problem';
        CHOOSECONTRACT : '\\chooseContract';
        PROOFOBLIGATION : '\\proofObligation';
        PROOF : '\\proof';
        CONTRACTS : '\\contracts';
        INVARIANTS : '\\invariants';

        // The first two guys are not really meta operators, treated separately
	IN_TYPE : '\\inType';
        IS_ABSTRACT_OR_INTERFACE : '\\isAbstractOrInterface';
        CONTAINERTYPE : '\\containerType';

        LIMITED : '$lmtd';

        // types that need to be declared as keywords
        LOCSET : '\\locset';
        SEQ : '\\seq';
        BIGINT : '\\bigint';

    // Unicode symbols for special functions/predicates
    UTF_PRECEDES : '\u227A';
    UTF_IN : '\u220A';
    UTF_EMPTY : '\u2205';
    UTF_UNION : '\u222A';
    UTF_INTERSECT : '\u2229';
    UTF_SUBSET : '\u2286';
    UTF_SETMINUS : '\u2216';

fragment
VOCAB
   :       '\u0003'..'\u0377'
   ;

SEMI
@init { paraphrase.push("`;'"); }
@after { paraphrase.pop(); }
:	';'
    ;

SLASH
@init { paraphrase.push("`/'"); }
@after { paraphrase.pop(); }
:	'/'
    ;

COLON
    @init { paraphrase.push("`:'"); }
@after { paraphrase.pop(); }
:    ':'
    ;

DOUBLECOLON
@init { paraphrase.push("Double `:'"); }
@after { paraphrase.pop(); }
:    '::'
  ;

ASSIGN
    @init { paraphrase.push("`:='"); }
@after { paraphrase.pop(); }
:    ':='
    ;

DOT
@init { paraphrase.push("`.'"); }
@after { paraphrase.pop(); }
:	'.'
	;

DOTRANGE
@init { paraphrase.push("`..'"); }
@after { paraphrase.pop(); }
:	'.' '.'
	;

COMMA
@init { paraphrase.push("`,'"); }
@after { paraphrase.pop(); }
:	','
	;

LPAREN
@init { paraphrase.push("`('"); }
@after { paraphrase.pop(); }
:
	'('
	;

RPAREN
@init { paraphrase.push("`)'"); }
@after { paraphrase.pop(); }
:	')'
    ;

LBRACE
@init { paraphrase.push("`{'"); }
	@after { paraphrase.pop(); }
:	'{'
	;

RBRACE
@init { paraphrase.push("`}'"); }
@after { paraphrase.pop(); }
:	'}'
    ;

LBRACKET
@init { paraphrase.push("`['"); }
@after { paraphrase.pop(); }
:	'['
    ;

RBRACKET
@init { paraphrase.push("`]'"); }
@after { paraphrase.pop(); }
:	']'
	;

EMPTYBRACKETS
@init { paraphrase.push("a pair of empty brackets []"); }
@after { paraphrase.pop(); }
:	'[' ']'
	;

AT
@init { paraphrase.push("`at'"); }
@after { paraphrase.pop(); }
:	'@'
	;

PARALLEL
@init { paraphrase.push("`parallel'"); }
@after { paraphrase.pop(); }
:     '|' '|'
	;


OR
@init { paraphrase.push("`|'"); }
@after { paraphrase.pop(); }
:	'|' | '\u2228'
	;

AND
@init { paraphrase.push("`&'"); }
@after { paraphrase.pop(); }
:	'&' | '\u2227'
	;

NOT
@init { paraphrase.push("`!'"); }
@after { paraphrase.pop(); }
:	'!' | '\u00AC'
	;

IMP
@init { paraphrase.push("`->'"); }
@after { paraphrase.pop(); }
:	'->' | '\u2192'
	;

EQUALS
@init { paraphrase.push("`='"); }
	@after { paraphrase.pop(); }
:	'='
	;

NOT_EQUALS
@init { paraphrase.push("`!='"); }
	@after { paraphrase.pop(); }
:	'!=' | '\u2260'
	;

SEQARROW
@init { paraphrase.push("`==>'"); }
	@after { paraphrase.pop(); }
:	'==>'
	;

EXP
@init { paraphrase.push("'^'"); }
	@after { paraphrase.pop(); }
:	'^'
	;

TILDE
@init { paraphrase.push("'~'"); }
	@after { paraphrase.pop(); }
:	'~'
	;

PERCENT
@init { paraphrase.push("`\%'"); }
@after { paraphrase.pop(); }
:   '%'
      ;

STAR
@init { paraphrase.push("`*'"); }
@after { paraphrase.pop(); }
:   '*'
      ;

MINUS
@init { paraphrase.push("`-'"); }
@after { paraphrase.pop(); }
:   '-'
      ;

PLUS
@init { paraphrase.push("`+'"); }
@after { paraphrase.pop(); }
:   '+'
      ;

GREATER
@init { paraphrase.push("`>'"); }
@after { paraphrase.pop(); }
:   '>'
      ;

GREATEREQUAL
@init { paraphrase.push("`>='"); }
@after { paraphrase.pop(); }
:   '>' '=' | '\u2265'
      ;

RGUILLEMETS
@init { paraphrase.push("`>>'"); }
@after { paraphrase.pop(); }
      :   '>' '>'
      ;


WS
@init { paraphrase.push("white space"); }
@after { paraphrase.pop(); }
:       (' '
      |       '\t'
      |       '\n'  { newline(); }
      |       '\r'  {if(input.LA(1) != '\n') newline();} )
	      { $channel = HIDDEN; }
      ;

STRING_LITERAL
@init { paraphrase.push("a string in double quotes"); StringBuilder _literal = new StringBuilder(); }
@after { paraphrase.pop(); setText('"' + _literal.toString() + '"'); }
: '"' (  ESC { _literal.append(getText()); }
       | newline='\n' { newline(); _literal.appendCodePoint(newline); }
       | normal=~('\n' | '"' | '\\' | '\uFFFF') { _literal.appendCodePoint(normal); }
      )*
  '"' ;


LESS_DISPATCH
@after { paraphrase.pop(); }
:
     ('<' (LETTER)+ '>') => IMPLICIT_IDENT {$type = IDENT;}
    |
     ('<' '-' '>') => EQV {$type = EQV;}
    |
     ('<' '=' ) => LESSEQUAL {$type = LESSEQUAL;}
    |
     ('<' '<' ) => LGUILLEMETS {$type = LGUILLEMETS;}
    |
     LESS {$type = LESS;}
    ;

fragment LESS
@init { paraphrase.push("'<'"); }
@after { paraphrase.pop(); }
:
  '<'
;

fragment LESSEQUAL
@init { paraphrase.push("'<='"); }
@after { paraphrase.pop(); }
:
  '<' '=' | '\u2264'
    ;

fragment LGUILLEMETS
@init { paraphrase.push("'<<'"); }
@after { paraphrase.pop(); }
:
  '<' '<'
    ;


fragment IMPLICIT_IDENT
@init { paraphrase.push("an implicit identifier (letters only)"); }
@after { paraphrase.pop(); }
:
  '<' (LETTER)+ '>'
;

fragment EQV
@init { paraphrase.push("`<->'"); }
@after { paraphrase.pop(); }
:	'<->' | '\u2194'
;

PRIMES_OR_CHARLITERAL
@after { paraphrase.pop(); }
:
     ('\'' '\'') => PRIMES {$type = PRIMES;}
    |
     ('\'' '\\') => CHAR_LITERAL {$type = CHAR_LITERAL;}
    |
     ('\'' ~('\'') '\'') => CHAR_LITERAL {$type = CHAR_LITERAL;}
    |
     PRIMES {$type = PRIMES;}
    ;


fragment
PRIMES
@init { paraphrase.push("Sequence of primes (at least one)"); }
	@after { paraphrase.pop(); }
:	('\'')+
	;

fragment
CHAR_LITERAL
@init { paraphrase.push("a char in single quotes"); }
@after { paraphrase.pop(); }
: '\''
                ((' '..'&') |
                 ('('..'[') |
                 (']'..'~') |
                 ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"' | 'u' HEX ))
                )
      '\''
 ;

fragment
ESC
@after { paraphrase.pop(); }
:	'\\'
    (	'n'         { setText("\n"); }
	|	'r' { setText("\r"); }
	|	't' { setText("\t"); }
	|	'b' { setText("\b"); }
	|	'f' { setText("\f"); }
	|	'"' { setText("\""); }
	|	'\'' { setText("'"); }
	|	'\\' { setText("\\"); }
	|	':' { setText ("\\:"); }
	|	' ' { setText ("\\ "); }
    )
    ;

fragment
QUOTED_STRING_LITERAL
@init { paraphrase.push("a string with double quotes"); }
    : '"' ('\\' . | '\n' {newline();} | ~('\n' | '"' | '\\') )* '"' ;

SL_COMMENT
@init { paraphrase.push("a comment"); }

	@after { paraphrase.pop(); }
:
	'//'
	(~('\n' | '\uFFFF'))* ('\n' | '\uFFFF' | EOF)
	{ $channel = HIDDEN; newline(); }
	;

ML_COMMENT
@init { paraphrase.push("a comment"); }
	@after { paraphrase.pop(); }
:
	'/*' {
	  while(true) {
	    if((input.LA(1) == '\r' && input.LA(2) != '\n') ||
		input.LA(1) == '\n') newline();
	    if(input.LA(1) == '*' && input.LA(2) == '/') {
	      match("*/");
	      break;
	    }
	    if (input.LA(1) == EOF) {
		throw new NoViableAltException("Matched EOF", -1, -1, input);
	    } else {
		input.consume();
	    }
	  }
	  $channel = HIDDEN;
	}
	;

// A single Digit that is followed by a ( is an ident, otherwise it's a number

DIGIT_DISPATCH
@after { paraphrase.pop(); }
:
    (DIGIT (' ' | '\t' | '\r' | '\n')* LPAREN) => DIGIT {$type = IDENT;}
  | ('0' 'x') => HEX_LITERAL {$type = NUM_LITERAL;}
  | NUM_LITERAL {$type = NUM_LITERAL;}
;

fragment
HEX_LITERAL
@init { paraphrase.push("a hexadeciaml constant"); }
	@after { paraphrase.pop(); }
: '0' 'x' (DIGIT | 'a'..'f' | 'A'..'F')+
	;

fragment
DIGIT
@init { paraphrase.push("a digit"); }
	@after { paraphrase.pop(); }
:	'0'..'9'
	;


fragment
HEX
@init { paraphrase.push("a hexadeciamal number"); }
@after { paraphrase.pop(); }
:	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
    ;

fragment
LETTER
@init { paraphrase.push("a letter"); }
@after { paraphrase.pop(); }
:	'a'..'z'|'A'..'Z'
    ;


fragment IDCHAR
@init { paraphrase.push("an admissible character for identifiers"); }
	@after { paraphrase.pop(); }
: LETTER | DIGIT | '_' | '#' | '$'
	;

IDENT
@init {
    paraphrase.push("an identifer");
}

@after { paraphrase.pop(); }
:  ( (LETTER | '_' | '#' | '$') (IDCHAR)*
    )
;

fragment
NUM_LITERAL
@init { paraphrase.push("a number"); }
@after { paraphrase.pop(); }
:
    (DIGIT)+
    ;

/**
  * Here we have to accept all strings of kind \\[a-z_]
  * and make the decision our selves as to what to do with it
  * (i.e. is it a modality, keyword, or possibly something else)
  */
MODALITY
@init {
    paraphrase.push("All possible modalities, including schema.");
    int _begin = getText().length();
}
@after { paraphrase.pop(); }
:	'\\' ( (LETTER | '_')+ | '<' | '[' | '[[') {
    modalityBegin = getText();
    Debug.out("modalityBegin == ", modalityBegin);
    //int literalTest = testLiteralsTable(MODALITY);
    //Debug.out("testLiteralsTable == ", literalTest);
    //$type = testLiteralsTable($type);
    if(/*literalTest == MODALITY && */modPairs.get(modalityBegin) != null) {
        /* This while with the following call to mMODALITYEND is
         * and alternative to calling mJAVABLOCK, but it should be faster
         */
        while(true) {
            if(input.LA(1) == '/' && input.LA(2) == '/') {
                mSL_COMMENT(); continue;
            }
            if(input.LA(1) == '/' && input.LA(2) == '*') {
                mML_COMMENT(); continue;
            }
            if(input.LA(1) == '/' && input.LA(2) == '*') {
                mML_COMMENT(); continue;
            }
            if(input.LA(1) == '\"') {
                mQUOTED_STRING_LITERAL(); continue;
            }
            if(input.LA(1) == '\'') {
                mCHAR_LITERAL(); continue;
            }
            if((input.LA(1) == '\r' && input.LA(2) != '\n') ||
                    input.LA(1) == '\n') newline();
            if(input.LA(1) == '\\' && (input.LA(2) == 'e' || input.LA(2) == '>' || input.LA(2) == ']'))
                // check whether it follows an ENDMODALITY
                break;
            if (input.LA(1) == EOF) {
                throw new NoViableAltException("Matched EOF", -1, -1, input);
            } else {
                input.consume();
            }
        }
        mMODALITYEND();
        //              mJAVABLOCK(false);
        matchAndTransformModality(_begin);
    }else{
        if("\\includeFile".equals(modalityBegin)) {
            // File inclusion
            while(input.LA(1) == ' ' || input.LA(1) == '\t' || input.LA(1) == '\n')
                match(input.LA(1));
            int startIndex = getText().length()+1;
            mQUOTED_STRING_LITERAL();
            int stopIndex = getText().length()-1;
            while(input.LA(1) == ' ' || input.LA(1) == '\t' || input.LA(1) == '\n')
                match(input.LA(1));
            mSEMI();
            $channel = HIDDEN;
            String fileName = getText().toString().substring(startIndex,stopIndex);
            Debug.out("File to be included: ", fileName);
            File incf = new File(fileName);
            File f = new File(getSourceName());
            if((f.isAbsolute() || f.getParentFile() != null) && !incf.isAbsolute()) {
                f = new File(f.getParentFile(), fileName);
                fileName = f.getAbsolutePath();
            }
            Debug.out("File to be included: ", fileName);
            try {
                // save current lexer's state
                SaveStruct ss = new SaveStruct(input);
                selector.push(ss);

                Debug.out("Pushed lexer.");

                // switch on new input stream
                setCharStream(new ANTLRFileStream(fileName));
                reset();
            } catch (IOException fnf) {
                throw new NoViableAltException("File '" + fileName + "' not found. (" +
                        getSourceName() + ", " + getLine() + ", " + getCharPositionInLine() + ")", -1, -1, input);
            }
        } else {
            $type = IDENT; // make it an IDENT starting with '\\'
            // (it will not contain digits!)
        }
    }
}
;

fragment MODALITYEND
@init{ int _begin = getText().length(); }
:	'\\' ( 'endmodality' | '>' | ']' | ']]')  {
	   modalityEnd = getText().substring(_begin);
           Debug.out("modalityEnd == ", modalityEnd);
	}
	;

fragment
JAVABLOCK
:
    (
	SL_COMMENT
      | ML_COMMENT
      | '/' ~('/' | '*')
      | CHAR_LITERAL
      | QUOTED_STRING_LITERAL
      | '\r' {if(input.LA(1) != '\n') newline();}
      | '\n' {newline(); }
      | 'a'..'z' | 'A'..'Z' | '_'
      | '0'..'9'
      | ' ' | '\t'
      | '{' | '}' | '(' | ')' | '[' | ']' | '<' | '>'
      | '.' | ',' | ';' | ':' | '?'
      | '%' | '*' | '-' | '=' | '+' | '~' | '&' | '|' | '^'
      | '!' | '@' | '#' | '$'
    )* MODALITYEND
   ;

