// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

/* -*-Antlr-*- */

header {
    package de.uka.ilkd.key.parser;

    import java.io.InputStream;
    import de.uka.ilkd.key.util.*;
    import java.util.HashMap;
    import java.util.LinkedHashMap;
    import antlr.TokenStreamSelector;
    import java.util.NoSuchElementException;
    import java.io.*;
}

/**
 * The common lexer for declarations, terms, formulae, Taclets, etc.
 */

class KeYLexer extends Lexer;
options {
    k=2;
    defaultErrorHandler = true;
    charVocabulary='\u0000'..'\uFFFE';
}

tokens {
        // Keywords used in sort declarations
	SORTS="\\sorts";
	GENERIC = "\\generic";
        EXTENDS = "\\extends";
        ONEOF = "\\oneof";
	ABSTRACT = "\\abstract";        

        // Keywords used in schema variable declarations
	SCHEMAVARIABLES = "\\schemaVariables";
	SCHEMAVAR = "\\schemaVar";
	MODALOPERATOR = "\\modalOperator";
	PROGRAM = "\\program";
	FORMULA = "\\formula";
	TERM = "\\term";
	UPDATE = "\\update";
	VARIABLES = "\\variables";
	SKOLEMTERM = "\\skolemTerm";
	SKOLEMFORMULA = "\\skolemFormula";
	
        // used in contracts
	MODIFIES = "\\modifies";

        // Keywords used in program variable declarations
	PROGRAMVARIABLES = "\\programVariables";

        // Keywords for varcond and related stuff
	VARCOND = "\\varcond";
	APPLY_UPDATE_ON_RIGID = "\\applyUpdateOnRigid";
        DEPENDINGON = "\\dependingOn";
	DISJOINTMODULONULL  = "\\disjointModuloNull";
	DROP_EFFECTLESS_ELEMENTARIES = "\\dropEffectlessElementaries";
	DROP_EFFECTLESS_STORES = "\\dropEffectlessStores";	
	SIMPLIFY_IF_THEN_ELSE_UPDATE = "\\simplifyIfThenElseUpdate";
	ENUM_CONST = "\\enumConstant";	
        FREELABELIN = "\\freeLabelIn";
	HASSORT = "\\hasSort";
	FIELDTYPE = "\\fieldType";
	ELEMSORT = "\\elemSort";        
	ISARRAY="\\isArray";
	ISARRAYLENGTH="\\isArrayLength";
        ISENUMTYPE="\\isEnumType";
	ISINDUCTVAR="\\isInductVar";	
	ISLOCALVARIABLE = "\\isLocalVariable";
	ISOBSERVER = "\\isObserver";
	DIFFERENT = "\\different";		
	METADISJOINT = "\\metaDisjoint";
	ISTHISREFERENCE="\\isThisReference";	        
	DIFFERENTFIELDS="\\differentFields";	        
	ISREFERENCE="\\isReference";	        
	ISREFERENCEARRAY="\\isReferenceArray";
	ISSUBTYPE = "\\sub";	
	EQUAL_UNIQUE = "\\equalUnique";
        NEW = "\\new";
        NEWLABEL = "\\newLabel";
	NOT = "\\not";
        NOTFREEIN = "\\notFreeIn";
	SAME = "\\same";
	STATIC = "\\static";
        STATICMETHODREFERENCE = "\\staticMethodReference";	
	STRICT    = "\\strict";	
	TYPEOF = "\\typeof";
	INSTANTIATE_GENERIC = "\\instantiateGeneric";

	// Quantifiers, binding, substitution
        FORALL = "\\forall";
        EXISTS = "\\exists";
        SUBST  = "\\subst";
	IF   = "\\if";
	IFEX   = "\\ifEx";
	THEN = "\\then";
	ELSE = "\\else";

        // inclusion and stuff, things that (usually) come at the beginnig 
	// of the file
	INCLUDE="\\include";
	INCLUDELDTS="\\includeLDTs";
	CLASSPATH="\\classpath";
	BOOTCLASSPATH="\\bootclasspath";
	NODEFAULTCLASSES="\\noDefaultClasses";
	JAVASOURCE="\\javaSource";
        WITHOPTIONS="\\withOptions";
        OPTIONSDECL="\\optionsDecl";
	KEYSETTINGS = "\\settings";
        PROFILE = "\\profile";

        // Those guys can stay being keywords
	TRUE = "true";
	FALSE = "false";

        // Keywords related to taclets
        SAMEUPDATELEVEL = "\\sameUpdateLevel";
        INSEQUENTSTATE = "\\inSequentState";
        ANTECEDENTPOLARITY = "\\antecedentPolarity";
        SUCCEDENTPOLARITY = "\\succedentPolarity";
        CLOSEGOAL = "\\closegoal";
        HEURISTICSDECL = "\\heuristicsDecl";
	NONINTERACTIVE = "\\noninteractive";
        DISPLAYNAME = "\\displayname";
        HELPTEXT = "\\helptext";
        REPLACEWITH = "\\replacewith";
        ADDRULES = "\\addrules";
        ADDPROGVARS = "\\addprogvars";
        HEURISTICS = "\\heuristics";	
	FIND = "\\find";
	ADD = "\\add";
	ASSUMES = "\\assumes";
	TRIGGER = "\\trigger";
	AVOID = "\\avoid";

	PREDICATES = "\\predicates";
	FUNCTIONS = "\\functions";
	UNIQUE = "\\unique";

	RULES = "\\rules";
        PROBLEM = "\\problem";
        CHOOSECONTRACT = "\\chooseContract";
        PROOFOBLIGATION = "\\proofObligation";
        PROOF = "\\proof";
        CONTRACTS = "\\contracts";
        INVARIANTS = "\\invariants";

        // The first two guys are not really meta operators, treated separately
	IN_TYPE = "\\inType";
        IS_ABSTRACT_OR_INTERFACE = "\\isAbstractOrInterface";
        CONTAINERTYPE = "\\containerType";
        
        LIMITED = "$lmtd";
        
        // types that need to be declared as keywords
        LOCSET = "\\locset";
        SEQ = "\\seq";
        BIGINT = "\\bigint";
}

{
    protected KeYExceptionHandler keh = new KeYRecoderExcHandler();
    protected TokenStreamSelector selector;

    // why is keh sometimes null?

    public KeYLexer(InputStream in, KeYExceptionHandler keh){
        this(in);
	if(keh != null)
            this.keh = keh; 
	this.selector = new TokenStreamSelector();
	selector.select(this);
    }
    
    public KeYLexer(InputStream in, KeYExceptionHandler keh, 
                    TokenStreamSelector selector){
        this(in);
	if(keh != null)
          this.keh = keh; 
	this.selector = selector;
    }
    
    public KeYLexer(Reader in, KeYExceptionHandler keh) {
        this(new CharBuffer(in));
	if(keh != null)
          this.keh = keh; 
	this.selector = new TokenStreamSelector();
	selector.select(this);
    }

    public void reportError(RecognitionException ex){
        keh.reportException(ex);
    }
    
    public TokenStreamSelector getSelector() {
      return selector;
    }

    public void uponEOF() throws TokenStreamException, CharStreamException {
      try {
         selector.pop(); // return to old lexer/stream
         Debug.out("Popped lexer.");
         selector.retry();
      } catch (NoSuchElementException e) {
         // return a real EOF if nothing in stack
      }
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
   
   public void recover( RecognitionException ex, BitSet tokenSet ) throws CharStreamException {
     consume();
     consumeUntil( tokenSet );
   }

   private void matchAndTransformModality(int beginIndex) throws antlr.RecognitionException {
      if(!modalityEnd.equals((String)modPairs.get(modalityBegin)))
          throw new RecognitionException("Unknown modality " +
	   "expression "+modalityBegin+"..."+modalityEnd+".",
	     getFilename(), getLine(), getColumn());

      antlr.ANTLRStringBuffer newText = new antlr.ANTLRStringBuffer();
      int index = 0;
      int first = 0;
      int last = 0;
      String s = text.toString();
      newText.append(s.substring(0,beginIndex));
      index = beginIndex + modalityBegin.length();
      String modName = "";
      if("\\modality".equals(modalityBegin)) {
         // Have to extract the name of (schema) modality inside the first {}
	 while(s.charAt(index) == ' ' || s.charAt(index) == '\t' ||
      	       s.charAt(index) == '\n' || s.charAt(index) == '\r') index++;
	 if(s.charAt(index) != '{') {
           throw new RecognitionException("Expression "+modalityBegin+" should be followed by {...}.",
	     getFilename(), getLine(), getColumn());
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
            throw new RecognitionException("Expected '}', found "+s.charAt(index)+".", getFilename(), getLine(), getColumn());
         }
	 index++;
	 modName=s.substring(first,last);
	 if("".equals(modName)) {
            throw new RecognitionException("Empty modality name. Modality block	was: "+s, getFilename(), getLine(), getColumn());
	 }
      }else{
         modName = (String)modNames.get(modalityBegin);
	 if(modName==null) {
            throw new RecognitionException("Unknown modality "+modalityBegin+".", getFilename(), getLine(), getColumn());
	 }

      }
      newText.append(modName+"\n");
      Debug.out("Modality name :", modName);
      last = s.lastIndexOf(modalityEnd);
      newText.append(s.substring(index,last));
      text = newText;
      Debug.out("Lexer: recognised Java block string: ", text);
   }

}

protected
VOCAB
   :       '\3'..'\377'
   ;

SEMI
options {
  paraphrase = "`;'";
} :	';'
    ;

SLASH
options {
  paraphrase = "`/'";
} :	'/'
    ;

COLON
    options {
    paraphrase = "`:'";
} :    ':'
    ;

DOUBLECOLON
options {
    paraphrase = "Double `:'";
} :    "::"
  ;

ASSIGN
    options {
    paraphrase = "`:='";
} :    ":="
    ;

DOT
options {
  paraphrase = "`.'";
}
	:	'.'
	;

DOTRANGE
options {
  paraphrase = "`..'";
}
	:	'.' '.'
	;

COMMA
options {
  paraphrase = "`,'";
}
	:	','
	;

LPAREN
options {
  paraphrase = "`('";
}
	:
	'(' 
	;

RPAREN
options {
    paraphrase = "`)'";
}
:	')'
    ;

LBRACE
options {
  paraphrase = "`{'";
}
	:	'{'
	;

RBRACE
options {
    paraphrase = "`}'";
}
:	'}'
    ;

LBRACKET
options {
    paraphrase = "`['";
}
:	'['
    ;

RBRACKET
options{
    paraphrase = "']'";
}
:	']'
	;

EMPTYBRACKETS
options{
    paraphrase = "a pair of empty brackets []";
}
:	'[' ']'
	;

AT
options {
    paraphrase = "`at'";
}
:	'@'
	;

PARALLEL
options {
   paraphrase = "`parallel'";  
}
:     '|' '|'
	;


OR
options {
  paraphrase = "`|'";
}
	:	'|'
	;

AND
options {
  paraphrase = "`&'";
}
	:	'&'
	;

NOT
options {
  paraphrase = "`!'";
}
	:	'!'
	;

IMP
options {
  paraphrase = "`->'";
}
	:	"->"
	;

EQUALS
options {
  paraphrase = "`='";
}
	:	"="
	;

NOT_EQUALS
options {
  paraphrase = "`!='";
}
	:	"!="
	;

SEQARROW
options {
  paraphrase = "`==>'";
}
	:	"==>"
	;

EXP
options { 
  paraphrase = "'^'";
}
	:	'^'
	;

TILDE
options { 
  paraphrase = "'~'";
}
	:	'~'
	;

PERCENT 
options {
  paraphrase = "`%'";
}
      :   '%'
      ;

STAR
options {
  paraphrase = "`*'";
}
      :   '*'
      ;

MINUS
options {
  paraphrase = "`-'";
}
      :   '-'
      ;

PLUS
options {
  paraphrase = "`+'";
}
      :   '+'
      ;

GREATER
options {
  paraphrase = "`>'";
}
      :   '>'
      ;

GREATEREQUAL
options {
  paraphrase = "`>='";
}
      :   '>' '='
      ;

RGUILLEMETS
options {
  paraphrase = "`>>'";
}
      :   '>' '>'
      ;


WS
options {
  paraphrase = "white space";
}
      :       (' '
      |       '\t'
      |       '\n'  { newline(); }
      |       '\r'  {if(LA(1) != '\n') newline();} )
	      { $setType(Token.SKIP); }
      ;

STRING_LITERAL
options {
  paraphrase = "a string in double quotes";
}
    : '"' ( ESC | '\n' { newline(); } |~('\n' | '"' | '\\' | '\uFFFF') )* '"' ;


LESS_DISPATCH
     :
     ('<' (LETTER)+ '>') => IMPLICIT_IDENT {$setType(IDENT);}
    |
     ('<' '-' '>') => EQV {$setType(EQV);}
    |
     ('<' '=' ) => LESSEQUAL {$setType(LESSEQUAL);}
    |
     ('<' '<' ) => LGUILLEMETS {$setType(LGUILLEMETS);}
    |
     LESS {$setType(LESS);}
    ;

protected LESS
options {
  paraphrase = "'<'";
}
:
  '<'
;

protected LESSEQUAL
options {
  paraphrase = "'<='";
}
:
  '<' '='
    ;

protected LGUILLEMETS
options {
  paraphrase = "'<<'";
}
:
  '<' '<'
    ;


protected IMPLICIT_IDENT
options {
  paraphrase = "an implicit identifier (letters only)";
}
:
  '<' (LETTER)+ '>'
;

protected EQV
options {
  paraphrase = "`<->'";
}
:	"<->"
;

PRIMES_OR_CHARLITERAL
     :
     ('\'' '\'') => PRIMES {$setType(PRIMES);}
    |
     ('\'' '\\') => CHAR_LITERAL {$setType(CHAR_LITERAL);}
    |
     ('\'' ~('\'') '\'') => CHAR_LITERAL {$setType(CHAR_LITERAL);}
    |
     PRIMES {$setType(PRIMES);}
    ;


protected
PRIMES
options {
  paraphrase = "Sequence of primes (at least one)";
}
	:	('\'')+
	;

protected
CHAR_LITERAL 
options {
  paraphrase = "a char in single quotes";
}
    : '\'' 
                ((' '..'&') |
                 ('('..'[') |
                 (']'..'~') |
                 ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"' | 'u' HEX ))
                )
      '\''
 ;

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
	|	':' { $setText ("\\:"); }
	|	' ' { $setText ("\\ "); }
    )
    ;

protected
QUOTED_STRING_LITERAL
options {
  paraphrase = "a string with double quotes";
}
    : '"' ('\\' . | '\n' {newline();} | ~('\n' | '"' | '\\') )* '"' ;
    
SL_COMMENT
options {
  paraphrase = "a comment";
}

	:
	"//"
	(~('\n' | '\uFFFF'))* ('\n' | '\uFFFF')
	{ $setType(Token.SKIP); newline(); }
	;

ML_COMMENT
options {
  paraphrase = "a comment";
}
	:
	"/*" {
	  while(true) {
	    if((LA(1) == '\r' && LA(2) != '\n') ||
		LA(1) == '\n') newline();
	    if(LA(1) == '*' && LA(2) == '/') {
	      match("*/");
	      break;
	    }
	    matchNot(EOF_CHAR);
	  }
	  $setType(Token.SKIP);
	}
	;

// A single Digit that is followed by a ( is an ident, otherwise it's a number

DIGIT_DISPATCH
:
    (DIGIT (' ' | '\t' | '\r' | '\n')* LPAREN) => DIGIT {$setType(IDENT);}
  | ('0' 'x') => HEX_LITERAL {$setType(NUM_LITERAL);}
  | NUM_LITERAL {$setType(NUM_LITERAL);}
;

protected
HEX_LITERAL
options {
  paraphrase = "a hexadeciaml constant";
}
	: '0' 'x' (DIGIT | 'a'..'f' | 'A'..'F')+
	;

protected
DIGIT
options {
  paraphrase = "a digit";
}
	:	'0'..'9'
	;


protected 
HEX
options {
    paraphrase = "a hexadeciamal number";
}
:	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
    ;

protected
LETTER
options {
    paraphrase = "a letter";
}
:	'a'..'z'|'A'..'Z' 
    ;


protected IDCHAR 
options {
	paraphrase = "an admissible character for identifiers";
}
	: LETTER | DIGIT | '_' | '#' | '$'
	;

IDENT
options {
    testLiterals = true;
    paraphrase = "an identifer";
}

:  ( (LETTER | '_' | '#' | '$') (IDCHAR)* 
    )
;

protected
NUM_LITERAL
options {
    paraphrase = "a number";
}
    : 
    (DIGIT)+    
    ;

/**
  * Here we have to accept all strings of kind \\[a-z_]
  * and make the decision our selves as to what to do with it
  * (i.e. is it a modality, keyword, or possibly something else)
  */
MODALITY
options {
    testLiterals = true;
    paraphrase = "All possible modalities, including schema.";
}
:	'\\' ( (LETTER | '_')+ | "<" | "[" | "[[") {
    modalityBegin = text.toString();
    Debug.out("modalityBegin == ", modalityBegin);
    int literalTest = testLiteralsTable(MODALITY);
    Debug.out("testLiteralsTable == ", literalTest);
    _ttype = testLiteralsTable(_ttype);
    if(literalTest == MODALITY && modPairs.get(modalityBegin) != null) {
        /* This while with the following call to mMODALITYEND is 
         * and alternative to calling mJAVABLOCK, but it should be faster
         */
        while(true) {
            if(LA(1) == '/' && LA(2) == '/') {
                mSL_COMMENT(false); continue;
            }
            if(LA(1) == '/' && LA(2) == '*') {
                mML_COMMENT(false); continue;
            }
            if(LA(1) == '/' && LA(2) == '*') {
                mML_COMMENT(false); continue;
            }
            if(LA(1) == '\"') {
                mQUOTED_STRING_LITERAL(false); continue;
            }
            if(LA(1) == '\'') {
                mCHAR_LITERAL(false); continue;
            }
            if((LA(1) == '\r' && LA(2) != '\n') ||
                    LA(1) == '\n') newline();
            if(LA(1) == '\\' && (LA(2) == 'e' || LA(2) == '>' || LA(2) == ']'))
                // check whether it follows an ENDMODALITY
                break;
            matchNot(EOF_CHAR);
        }
        mMODALITYEND(false);
        //              mJAVABLOCK(false);
        matchAndTransformModality(_begin);
    }else{
        if("\\includeFile".equals(modalityBegin)) {
            // File inclusion 
            while(LA(1) == ' ' || LA(1) == '\t' || LA(1) == '\n')
                match(LA(1));
            int startIndex = text.length()+1;
            mQUOTED_STRING_LITERAL(false);
            int stopIndex = text.length()-1;
            while(LA(1) == ' ' || LA(1) == '\t' || LA(1) == '\n')
                match(LA(1));
            mSEMI(false);
            _ttype = Token.SKIP;
            String fileName = text.toString().substring(startIndex,stopIndex);
            Debug.out("File to be included: ", fileName);
            File incf = new File(fileName);
            File f = new File(getFilename());
            if((f.isAbsolute() || f.getParentFile() != null) && !incf.isAbsolute()) {
                f = new File(f.getParentFile(), fileName);
                fileName = f.getAbsolutePath();
            }
            Debug.out("File to be included: ", fileName);
            try {
                KeYLexer sublexer =
                    new KeYLexer(
                            new DataInputStream(new  
                                    FileInputStream(fileName)),
                                    keh, selector);
                sublexer.setFilename(fileName);
                selector.push(sublexer);
                Debug.out("Pushed lexer: ", sublexer);
                selector.retry();
            } catch (FileNotFoundException fnf) {
                throw new RecognitionException("File '" + fileName + "' not found.",
                        getFilename(), getLine(), getColumn());
            }
        } else {
            _ttype = IDENT; // make it an IDENT starting with '\\'
            // (it will not contain digits!)
        }
    }
}
;

protected MODALITYEND
options {
}
:	'\\' ( "endmodality" | ">" | "]" | "]]")  {
	   modalityEnd = new String(text.getBuffer(), _begin, text.length() - _begin);
           Debug.out("modalityEnd == ", modalityEnd);
	}
	;

protected
JAVABLOCK
 :
    (
	SL_COMMENT
      | ML_COMMENT 
      | '/' ~('/' | '*')
      | CHAR_LITERAL
      | QUOTED_STRING_LITERAL
      | '\r' {if(LA(1) != '\n') newline();}
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

