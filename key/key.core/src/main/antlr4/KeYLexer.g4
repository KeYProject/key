lexer grammar KeYLexer;

@header {
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

// Comments have precedence over operators // and /*.
SL_COMMENT
:
	'//'
	(~('\n' | '\uFFFF'))* ('\n' | '\uFFFF' | EOF) -> channel(HIDDEN)
;

DOC_COMMENT: '/*!' -> more, pushMode(docComment);
ML_COMMENT: '/*' OP_SFX? -> more, pushMode(COMMENT);


DATATYPES:'\\datatypes';
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
INFIX: '\\infix';
PREFIX: '\\prefix';
SHORTCUT:'\\shortcut';
POSTFIX: '\\postfix';

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
/*UTF_PRECEDES : '\u227A';
UTF_IN : '\u220A';
UTF_EMPTY : '\u2205';
UTF_UNION : '\u222A';
UTF_INTERSECT : '\u2229';
UTF_SUBSET : '\u2286';
UTF_SETMINUS : '\u2216';
*/

fragment
VOCAB
   :       '\u0003'..'\u0377'
   ;


SEMI:	 ';';
COLON: ':';
DOUBLECOLON:'::';
ASSIGN: ':=';
DOT:	  '.';
DOTRANGE:	'.' '.';
COMMA:	',';
LPAREN:	'(';
RPAREN:	')';
LBRACE:	'{';
RBRACE:	'}';
LBRACKET:	'[';
RBRACKET:	']';
EMPTYBRACKETS:	'[' ']';
PARALLEL: '|' '|';


/* Trailing characters of a
 */
fragment OP_SFX: ('-'|'='|'+'|'*'|'/'|'&'|'.'|'|'|'^'|':'|'>'|'<')+;

DOT_PLUS : '\u2214'; // ∔
MINUS_OR_PLUS: '\u2213'; //∓
SET_MINUS: '\u2216' | '\\setminus' ;// ∖
ASTERISK: '\u2217';//  ∗
RING: '\u2218'; //∘
CDOT: '\u2219';// ∙
DIVIDES: '\u2223';// (8739)	∣	DIVIDES	teilt
NOT_DIVIDES: '\u2224';// (8740)	∤	DOES NOT DIVIDE	teilt nicht
PARALLEL_TO: '\u2225';//(8741)	∥	PARALLEL TO	parallel zu
NOT_PARALLEL_TO: '\u2226' ;//(8742)	∦	NOT PARALLEL TO	nicht parallel zu
INTERSECT: '\u2229' ;//(8745)	∩	INTERSECTION	Schnittmengenzeichen
UNION: '\u222A' ;//(8746)	∪	UNION	Vereinigungsmengenzeichen
THEREFORE: '\u2234' ;//(8756)	∴	THEREFORE	folglich
BECAUSE: '\u2235' ;//(8757)	∵	BECAUSE	weil
RATION: '\u2236' ;//(8758)	∶	RATIO	Verhältniszeichen
PROPORTION: '\u2237' ;//(8759)	∷	PROPORTION	Proportionszeichen
DOT_MINUS: '\u2238' ;//(8760)	∸	DOT MINUS	Minuszeichen mit Punkt
EXCESS: '\u2239' ;//(8761)	∹	EXCESS	Exzess
GEOMETRIC_PROPORTION: '\u223A' ;//(8762)	∺	GEOMETRIC PROPORTION	geometrische Proportion
HOMOTHETIC: '\u223B' ;//(8763)	∻	HOMOTHETIC	Homothetiezeichen
REVERSE_TILDE: '\u223D' ;//(8765)	∽	REVERSED TILDE	umgekehrte Tilde
INVERTED_LAZY_S: '\u223E' ;//(8766)	∾	INVERTED LAZY S	invertiertes stummes S
SINE_WAVE: '\u223F' ;//(8767)	∿	SINE WAVE	Sinuswelle
WREATH_PRODUCT: '\u2240' ;//(8768)	≀	WREATH PRODUCT	Kranzprodukt
NOT_TILDE:'\u2241' ;//(8769)	≁	NOT TILDE	durchgestrichene Tilde
MINUS_TILDE: '\u2242' ;//(8770)	≂	MINUS TILDE	Minus über Tilde
ASYMP_EQUAL: '\u2243' ;// (8771)	≃	ASYMPTOTICALLY EQUAL TO	asymptotisch gleich
NOT_ASYMP_EQUAL: '\u2244' ;// (8772)	≄	NOT ASYMPTOTICALLY EQUAL TO	nicht asymptotisch gleich
/*
'\u2245' ;// (8773)	≅	APPROXIMATELY EQUAL TO	ungefähr gleich
'\u2246' ;// (8774)	≆	APPROXIMATELY BUT NOT ACTUALLY EQUAL TO	ungefähr, aber nicht genau gleich
'\u2247' ;// (8775)	≇	NEITHER APPROXIMATELY NOR ACTUALLY EQUAL TO	weder ungefähr noch genau gleich
'\u2248' ;// (8776)	≈	ALMOST EQUAL TO	fast gleich
'\u2249' ;// (8777)	≉	NOT ALMOST EQUAL TO	nicht fast gleich
'\u224A' ;// (8778)	≊	ALMOST EQUAL OR EQUAL TO	fast gleich oder gleich
'\u224B' ;// (8779)	≋	TRIPLE TILDE	dreifache Tilde
'\u224C' ;// (8780)	≌	ALL EQUAL TO	alles Gleich
'\u224D' ;// (8781)	≍	EQUIVALENT TO	äquivalent
'\u224E' ;// (8782)	≎	GEOMETRICALLY EQUIVALENT TO	geometrisch äquivalent
'\u224F' ;// (8783)	≏	DIFFERENCE BETWEEN	Differenz zwischen
'\u2250' ;// (8784)	≐	APPROACHES THE LIMIT	Grenzwertannäherung
'\u2251' ;// (8785)	≑	GEOMETRICALLY EQUAL TO	geometrisch gleich
'\u2252' ;// (8786)	≒	APPROXIMATELY EQUAL TO OR THE IMAGE OF	ungefähr gleich oder Bild von
'\u2253' ;// (8787)	≓	IMAGE OF OR APPROXIMATELY EQUAL TO	Bild oder ungefähr gleich
'\u2254' ;// (8788)	≔	COLON EQUALS	Gleichheitszeichen mit vorangestelltem Doppelpunkt' ;// (Definitionszeichen)
'\u2255' ;// (8789)	≕	EQUALS COLON	Gleichheitszeichen mit nachfolgendem Doppelpunkt
'\u2256' ;// (8790)	≖	RING IN EQUAL TO	Kreis im Gleichheitszeichen
'\u2257' ;// (8791)	≗	RING EQUAL TO	Kreis über Gleichheitszeichen' ;// (ungefähr gleich)
'\u2258' ;// (8792)	≘	CORRESPONDS TO	Entspricht-Zeichen' ;// (unüblich)
'\u2259' ;// (8793)	≙	ESTIMATES	entspricht
'\u225A' ;// (8794)	≚	EQUIANGULAR TO	gleichwinklig
'\u225B' ;// (8795)	≛	STAR EQUALS	Gleichheitszeichen mit Stern
'\u225C' ;// (8796)	≜	DELTA EQUAL TO	Gleichheitszeichen mit Delta
'\u225D' ;// (8797)	≝	EQUAL TO BY DEFINITION	gleich nach Definition
'\u225E' ;// (8798)	≞	MEASURED BY	gemessen nach
'\u225F' ;// (8799)	≟	QUESTIONED EQUAL TO	vielleicht gleich
'\u2260' ;// (8800)	≠	NOT EQUAL TO	Ungleichheitszeichen
'\u2261' ;// (8801)	≡	IDENTICAL TO	ist kongruent zu
'\u2262' ;// (8802)	≢	NOT IDENTICAL TO	ist nicht kongruent zu
'\u2263' ;// (8803)	≣	STRICTLY EQUIVALENT TO	genau äquivalent
'\u2264' ;// (8804)	≤	LESS-THAN OR EQUAL TO	kleiner/gleich
'\u2265' ;// (8805)	≥	GREATER-THAN OR EQUAL TO	größer/gleich
'\u2266' ;// (8806)	≦	LESS-THAN OVER EQUAL TO	kleiner als über gleich
'\u2267' ;// (8807)	≧	GREATER-THAN OVER EQUAL TO	größer als über gleich
'\u2268' ;// (8808)	≨	LESS-THAN BUT NOT EQUAL TO	kleiner als, aber nicht gleich
'\u2269' ;// (8809)	≩	GREATER-THAN BUT NOT EQUAL TO	größer als, aber nicht gleich
'\u226A' ;// (8810)	≪	MUCH LESS-THAN	viel kleiner als
'\u226B' ;// (8811)	≫	MUCH GREATER-THAN	viel größer als
'\u226C' ;// (8812)	≬	BETWEEN	zwischen
'\u226D' ;// (8813)	≭	NOT EQUIVALENT TO	nicht äquivalent
'\u226E' ;// (8814)	≮	NOT LESS-THAN	ist nicht kleiner als
'\u226F' ;// (8815)	≯	NOT GREATER-THAN	ist nicht größer als
'\u2270' ;// (8816)	≰	NEITHER LESS-THAN NOR EQUAL TO	weder kleiner als noch gleich
'\u2271' ;// (8817)	≱	NEITHER GREATER-THAN NOR EQUAL TO	weder größer als noch gleich
'\u2272' ;// (8818)	≲	LESS-THAN OR EQUIVALENT TO	kleiner als oder äquivalent
'\u2273' ;// (8819)	≳	GREATER-THAN OR EQUIVALENT TO	größer als oder äquivalent
'\u2274' ;// (8820)	≴	NEITHER LESS-THAN NOR EQUIVALENT TO	weder kleiner als noch äquivalent
'\u2275' ;// (8821)	≵	NEITHER GREATER-THAN NOR EQUIVALENT TO	weder größer als noch äquivalent
'\u2276' ;// (8822)	≶	LESS-THAN OR GREATER-THAN	kleiner/größer als
'\u2277' ;// (8823)	≷	GREATER-THAN OR LESS-THAN	größer/kleiner als
'\u2278' ;// (8824)	≸	NEITHER LESS-THAN NOR GREATER-THAN	weder kleiner noch größer als
'\u2279' ;// (8825)	≹	NEITHER GREATER-THAN NOR LESS-THAN	weder größer noch kleiner als
'\u227A' ;// (8826)	≺	PRECEDES	vorangehend
'\u227B' ;// (8827)	≻	SUCCEEDS	nachfolgend
'\u227C' ;// (8828)	≼	PRECEDES OR EQUAL TO	vorangehend oder gleich
'\u227D' ;// (8829)	≽	SUCCEEDS OR EQUAL TO	nachfolgend oder gleich
'\u227E' ;// (8830)	≾	PRECEDES OR EQUIVALENT TO	vorangehend oder äquivalent
'\u227F' ;// (8831)	≿	SUCCEEDS OR EQUIVALENT TO	nachfolgend oder äquivalent
'\u2280' ;// (8832)	⊀	DOES NOT PRECEDE	nicht vorangehend
'\u2281' ;// (8833)	⊁	DOES NOT SUCCEED	nicht nachfolgend
'\u2282' ;// (8834)	⊂	SUBSET OF	ist ;// (echte) Teilmenge von
'\u2283' ;// (8835)	⊃	SUPERSET OF	ist ;// (echte) Obermenge von
'\u2284' ;// (8836)	⊄	NOT A SUBSET OF	ist keine ;// (echte) Teilmenge von
'\u2285' ;// (8837)	⊅	NOT A SUPERSET OF	ist keine ;// (echte) Obermenge von
'\u2286' ;// (8838)	⊆	SUBSET OF OR EQUAL TO	Teilmenge oder gleich
'\u2287' ;// (8839)	⊇	SUPERSET OF OR EQUAL TO	Obermenge oder gleich
'\u2288' ;// (8840)	⊈	NEITHER A SUBSET OF NOR EQUAL TO	weder Teilmenge noch gleich
'\u2289' ;// (8841)	⊉	NEITHER A SUPERSET OF NOR EQUAL TO	weder Obermenge noch gleich
'\u228A' ;// (8842)	⊊	SUBSET OF WITH NOT EQUAL TO	Teilmenge mit ungleich
'\u228B' ;// (8843)	⊋	SUPERSET OF WITH NOT EQUAL TO	Obermenge mit ungleich
'\u228C' ;// (8844)	⊌	MULTISET	Multimenge
'\u228D' ;// (8845)	⊍	MULTISET MULTIPLICATION	Multimengenmultiplikation
'\u228E' ;// (8846)	⊎	MULTISET UNION	Multimengenvereinigung
'\u228F' ;// (8847)	⊏	SQUARE IMAGE OF	viereckiges Bild
'\u2290' ;// (8848)	⊐	SQUARE ORIGINAL OF	viereckiges Original
'\u2291' ;// (8849)	⊑	SQUARE IMAGE OF OR EQUAL TO	viereckiges Bild oder gleich
'\u2292' ;// (8850)	⊒	SQUARE ORIGINAL OF OR EQUAL TO	viereckiges Original oder gleich
'\u2293' ;// (8851)	⊓	SQUARE CAP	nach unten geöffnetes Viereck
'\u2294' ;// (8852)	⊔	SQUARE CUP	nach oben geöffnetes Viereck
'\u2295' ;// (8853)	⊕	CIRCLED PLUS	eingekreistes Pluszeichen
'\u2296' ;// (8854)	⊖	CIRCLED MINUS	eingekreistes Minuszeichen
'\u2297' ;// (8855)	⊗	CIRCLED TIMES	eingekreistes Multiplikationszeichen
'\u2298' ;// (8856)	⊘	CIRCLED DIVISION SLASH	eingekreister Divisionsstrich
'\u2299' ;// (8857)	⊙	CIRCLED DOT OPERATOR	eingekreister Punktoperator
'\u229A' ;// (8858)	⊚	CIRCLED RING OPERATOR	eingekreister Ringoperator
'\u229B' ;// (8859)	⊛	CIRCLED ASTERISK OPERATOR	eingekreister Sternoperator
'\u229C' ;// (8860)	⊜	CIRCLED EQUALS	eingekreistes Gleichheitszeichen
'\u229D' ;// (8861)	⊝	CIRCLED DASH	eingekreister Gedankenstrich
'\u229E' ;// (8862)	⊞	SQUARED PLUS	eingerahmtes Pluszeichen
'\u229F' ;// (8863)	⊟	SQUARED MINUS	eingerahmtes Minuszeichen
'\u22A0' ;// (8864)	⊠	SQUARED TIMES	eingerahmtes Multiplikationszeichen
'\u22A1' ;// (8865)	⊡	SQUARED DOT OPERATOR	eingerahmter Punktoperator
'\u22A2' ;// (8866)	⊢	RIGHT TACK	ergibt
'\u22A3' ;// (8867)	⊣	LEFT TACK	ergibt nicht
'\u22A4' ;// (8868)	⊤	DOWN TACK	senkrecht von
'\u22A5' ;// (8869)	⊥	UP TACK	senkrecht auf
'\u22A6' ;// (8870)	⊦	ASSERTION	Assertion
'\u22A7' ;// (8871)	⊧	MODELS	Modelle
'\u22A8' ;// (8872)	⊨	TRUE	wahr
'\u22A9' ;// (8873)	⊩	FORCES	erzwingen
'\u22AA' ;// (8874)	⊪	TRIPLE VERTICAL BAR RIGHT TURNSTILE	dreifache vertikale Leiste mit rechtem Drehkreuz
'\u22AB' ;// (8875)	⊫	DOUBLE VERTICAL BAR DOUBLE RIGHT TURNSTILE	doppelte vertikale Leiste mit doppeltem rechtem Drehkreuz
'\u22AC' ;// (8876)	⊬	DOES NOT PROVE	beweist nicht
'\u22AD' ;// (8877)	⊭	NOT TRUE	nicht wahr
'\u22AE' ;// (8878)	⊮	DOES NOT FORCE	nicht erzwingen
'\u22AF' ;// (8879)	⊯	NEGATED DOUBLE VERTICAL BAR DOUBLE RIGHT TURNSTILE	negierte doppelte vertikale Leiste mit doppeltem rechten Drehkreuz
'\u22B0' ;// (8880)	⊰	PRECEDES UNDER RELATION	vorangehend in Relation
'\u22B1' ;// (8881)	⊱	SUCCEEDS UNDER RELATION	nachfolgend in Relation
'\u22B2' ;// (8882)	⊲	NORMAL SUBGROUP OF	normale Untergruppe
'\u22B3' ;// (8883)	⊳	CONTAINS AS NORMAL SUBGROUP	als normale Untergruppe enthalten
'\u22B4' ;// (8884)	⊴	NORMAL SUBGROUP OF OR EQUAL TO	normale Untergruppe oder gleich
'\u22B5' ;// (8885)	⊵	CONTAINS AS NORMAL SUBGROUP OR EQUAL TO	als normale Untergruppe enthalten oder gleich
'\u22B6' ;// (8886)	⊶	ORIGINAL OF	Original
'\u22B7' ;// (8887)	⊷	IMAGE OF	Bild
'\u22B8' ;// (8888)	⊸	MULTIMAP	Mehrfachzuordnung
'\u22B9' ;// (8889)	⊹	HERMITIAN CONJUGATE MATRIX	hermitesch konjugierte Matrix
'\u22BA' ;// (8890)	⊺	INTERCALATE	einschalten
'\u22BB' ;// (8891)	⊻	XOR	Ausschließendes Oder
'\u22BC' ;// (8892)	⊼	NAND	Nand-verknüpft mit
'\u22BD' ;// (8893)	⊽	NOR	Nor
'\u22BE' ;// (8894)	⊾	RIGHT ANGLE WITH ARC	rechter Winkel mit Bogen
'\u22BF' ;// (8895)	⊿	RIGHT TRIANGLE	rechtes Dreieck
'\u22C0' ;// (8896)	⋀	N-ARY LOGICAL AND	N-stufiges logisches Und
'\u22C1' ;// (8897)	⋁	N-ARY LOGICAL OR	N-stufiges logisches Oder
'\u22C2' ;// (8898)	⋂	N-ARY INTERSECTION	N-stufiger Durchschnitt
'\u22C3' ;// (8899)	⋃	N-ARY UNION	N-stufige Vereinigung
'\u22C4' ;// (8900)	⋄	DIAMOND OPERATOR	Rautenoperator
'\u22C5' ;// (8901)	⋅	DOT OPERATOR	Multiplikationspunkt
'\u22C6' ;// (8902)	⋆	STAR OPERATOR	Sternoperator
'\u22C7' ;// (8903)	⋇	DIVISION TIMES	Divisionsanzahl
'\u22C8' ;// (8904)	⋈	BOWTIE	Schleife
'\u22C9' ;// (8905)	⋉	LEFT NORMAL FACTOR SEMIDIRECT PRODUCT	linkes halbdirektes Produkt' ;// (Normalfaktor)
'\u22CA' ;// (8906)	⋊	RIGHT NORMAL FACTOR SEMIDIRECT PRODUCT	rechtes halbdirektes Produkt' ;// (Normalfaktor)
'\u22CB' ;// (8907)	⋋	LEFT SEMIDIRECT PRODUCT	linkes halbdirektes Produkt
'\u22CC' ;// (8908)	⋌	RIGHT SEMIDIRECT PRODUCT	rechtes halbdirektes Produkt
'\u22CD' ;// (8909)	⋍	REVERSED TILDE EQUALS	umgekehrte Tilde gleich
'\u22CE' ;// (8910)	⋎	CURLY LOGICAL OR	geschweiftes logisches Oder
'\u22CF' ;// (8911)	⋏	CURLY LOGICAL AND	geschweiftes logisches Und
'\u22D0' ;// (8912)	⋐	DOUBLE SUBSET	doppelte Teilmenge
'\u22D1' ;// (8913)	⋑	DOUBLE SUPERSET	doppelte Obermenge
'\u22D2' ;// (8914)	⋒	DOUBLE INTERSECTION	doppelter Durchschnitt
'\u22D3' ;// (8915)	⋓	DOUBLE UNION	doppelte Vereinigung
'\u22D4' ;// (8916)	⋔	PITCHFORK	echter Durchschnitt
'\u22D5' ;// (8917)	⋕	EQUAL AND PARALLEL TO	gleich und parallel ;// (ähnlich dem Doppelkreuz)
'\u22D6' ;// (8918)	⋖	LESS-THAN WITH DOT	kleiner als mit Punkt
'\u22D7' ;// (8919)	⋗	GREATER-THAN WITH DOT	größer als mit Punkt
'\u22D8' ;// (8920)	⋘	VERY MUCH LESS-THAN	Sehr viel kleiner als
'\u22D9' ;// (8921)	⋙	VERY MUCH GREATER-THAN	sehr viel größer als
'\u22DA' ;// (8922)	⋚	LESS-THAN EQUAL TO OR GREATER-THAN	kleiner als, gleich oder größer als
'\u22DB' ;// (8923)	⋛	GREATER-THAN EQUAL TO OR LESS-THAN	größer als, gleich oder kleiner als
'\u22DC' ;// (8924)	⋜	EQUAL TO OR LESS-THAN	gleich oder kleiner als
'\u22DD' ;// (8925)	⋝	EQUAL TO OR GREATER-THAN	gleich oder größer als
'\u22DE' ;// (8926)	⋞	EQUAL TO OR PRECEDES	gleich oder vorangehend
'\u22DF' ;// (8927)	⋟	EQUAL TO OR SUCCEEDS	gleich oder nachfolgend
'\u22E0' ;// (8928)	⋠	DOES NOT PRECEDE OR EQUAL	weder vorangehend oder gleich
'\u22E1' ;// (8929)	⋡	DOES NOT SUCCEED OR EQUAL	weder nachfolgend oder gleich
'\u22E2' ;// (8930)	⋢	NOT SQUARE IMAGE OF OR EQUAL TO	kein viereckiges Bild oder gleich
'\u22E3' ;// (8931)	⋣	NOT SQUARE ORIGINAL OF OR EQUAL TO	kein viereckiges Original oder gleich
'\u22E4' ;// (8932)	⋤	SQUARE IMAGE OF OR NOT EQUAL TO	viereckiges Bild oder ungleich
'\u22E5' ;// (8933)	⋥	SQUARE ORIGINAL OF OR NOT EQUAL TO	viereckiges Original oder ungleich
'\u22E6' ;// (8934)	⋦	LESS-THAN BUT NOT EQUIVALENT TO	kleiner als, aber nicht äquivalent
'\u22E7' ;// (8935)	⋧	GREATER-THAN BUT NOT EQUIVALENT TO	größer als, aber nicht äquivalent
'\u22E8' ;// (8936)	⋨	PRECEDES BUT NOT EQUIVALENT TO	vorangehend, aber nicht äquivalent
'\u22E9' ;// (8937)	⋩	SUCCEEDS BUT NOT EQUIVALENT TO	nachfolgend, aber nicht äquivalent
'\u22EA' ;// (8938)	⋪	NOT NORMAL SUBGROUP OF	keine normale Untergruppe
'\u22EB' ;// (8939)	⋫	DOES NOT CONTAIN AS NORMAL SUBGROUP	nicht als normale Untergruppe enthalten
'\u22EC' ;// (8940)	⋬	NOT NORMAL SUBGROUP OF OR EQUAL TO	keine normale Untergruppe oder gleich
'\u22ED' ;// (8941)	⋭	DOES NOT CONTAIN AS NORMAL SUBGROUP OR EQUAL	nicht als normale Untergruppe enthalten oder gleich
'\u22EE' ;// (8942)	⋮	VERTICAL ELLIPSIS	Vertikale Ellipse
'\u22EF' ;// (8943)	⋯	MIDLINE HORIZONTAL ELLIPSIS	Zentrierte horizontale Ellipse
'\u22F0' ;// (8944)	⋰	UP RIGHT DIAGONAL ELLIPSIS	Diagonale Ellipse, unten links nach oben rechts
'\u22F1' ;// (8945)	⋱	DOWN RIGHT DIAGONAL ELLIPSIS	Diagonale Ellipse, oben links nach unten rechts
'\u22F2' ;// (8946)	⋲	ELEMENT OF WITH LONG HORIZONTAL STROKE	Element mit langem horizontalen Strich
'\u22F3' ;// (8947)	⋳	ELEMENT OF WITH VERTICAL BAR AT END OF HORIZONTAL STROKE	Element mit vertikalem Strich am Ende des horizontalen Strichs
'\u22F4' ;// (8948)	⋴	SMALL ELEMENT OF WITH VERTICAL BAR AT END OF HORIZONTAL STROKE	kleines Element mit vertikalem Strich am Ende des horizontalen Strichs
'\u22F5' ;// (8949)	⋵	ELEMENT OF WITH DOT ABOVE	Element mit Punkt ;// (oben)
'\u22F6' ;// (8950)	⋶	ELEMENT OF WITH OVERBAR	Element mit Überstrich
'\u22F7' ;// (8951)	⋷	SMALL ELEMENT OF WITH OVERBAR	kleines Element mit Überstrich
'\u22F8' ;// (8952)	⋸	ELEMENT OF WITH UNDERBAR	Element mit Unterstrich
'\u22F9' ;// (8953)	⋹	ELEMENT OF WITH TWO HORIZONTAL STROKES	Element mit 2 horizontalen Strichen
'\u22FA' ;// (8954)	⋺	CONTAINS WITH LONG HORIZONTAL STROKE	umgekehrtes Elementzeichen mit langem horizontalen Strich
'\u22FB' ;// (8955)	⋻	CONTAINS WITH VERTICAL BAR AT END OF HORIZONTAL STROKE	umgekehrtes Elementzeichen mit vertikalem Strich am Ende des horizontalen Strichs
'\u22FC' ;// (8956)	⋼	SMALL CONTAINS WITH VERTICAL BAR AT END OF HORIZONTAL STROKE	kleines umgekehrtes Elementzeichen mit vertikalem Strich am Ende des horizontalen Strichs
'\u22FD' ;// (8957)	⋽	CONTAINS WITH OVERBAR	umgekehrtes Elementzeichen mit Überstrich
'\u22FE' ;// (8958)	⋾	SMALL CONTAINS WITH OVERBAR	kleines umgekehrtes Elementzeichen mit Überstrich
'\u22FF' ;// (8959)	⋿	Z NOTATION BAG MEMBERSHIP
*/

SEQARROW:	'==>' | '\u27F9';
NOT_EQUALS:	'!=' OP_SFX? | '\u2260';
IMP:	'->' | '\u2192';
SLASH: '/' OP_SFX?;
AT:	'@' OP_SFX?;
OR:	'|' OP_SFX? | '\u2228';
AND:	'&' OP_SFX? | '\u2227';
NOT:	'!' (OP_SFX|'!')? | '\u00AC';
EQUALS:	'=' OP_SFX?;
EXP:	'^' OP_SFX?;
TILDE:	('~'|'\u223C') OP_SFX?;
PERCENT: '%' OP_SFX?;
STAR :   '*' OP_SFX?;
MINUS:   '-' OP_SFX?;
PLUS:    '+' OP_SFX?;
GREATER: '>' ;
GREATEREQUAL:   '>' '=' | '\u2265';
RGUILLEMETS: '>' '>' ;



WS:  [ \t\n\r\u00a0]+ -> channel(HIDDEN); //'\u00A0 = non breakable whitespace
STRING_LITERAL:'"' ('\\' . | ~( '"' | '\\') )* '"' ;

EQV:	'<->' | '\u2194';
LESSEQUAL: '<' '=' | '\u2264';
LGUILLEMETS: '<' '<';
LESS: '<' OP_SFX?;
IMPLICIT_IDENT: '<' (LETTER)+ '>' ('$lmtd')? -> type(IDENT);
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