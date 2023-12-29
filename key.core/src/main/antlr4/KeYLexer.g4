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

// Comments have precedence over operators // and /*.
SL_COMMENT
:
	'//'
	(~('\n' | '\uFFFF'))* ('\n' | '\uFFFF' | EOF) -> channel(HIDDEN)
;
DOC_COMMENT: '/*!' -> more, pushMode(docComment);
ML_COMMENT: '/*' -> more, pushMode(COMMENT);



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
FREE : '\\free';
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

fragment
VOCAB
   :       '\u0003'..'\u0377'
   ;

fragment OP_SFX: ('-'|'='|'+'|'*'|'/'|'&'|'.'|'|'|'^'|'!'|':'|'>'|'<');

RPAREN          : ')';
LPAREN          : '(';
RBRACE          : '}';
LBRACE          : '{';
LBRACKET        : '[';
RBRACKET        : ']';
PARALLEL        : '||';

SEMI:         ';';
COLON:        ':';
DOUBLECOLON:  '::';
ASSIGN:       ':=' | '\u2254' ;// (8788) ≔	COLON EQUALS
DOT:          '.';
DOTRANGE:	  '.' '.';
DOT_WITH_MORE:'.' OP_SFX*;
COMMA:	      ',';

SET_IN        : '\u220A' /*∊*/ | '\\in';
EMPTY     : '\u2205' /*∅*/ | '\\emptyset';
UNION     : '\u222A' /*∪*/ | '\\cup'; //(8746)	∪	UNION	Vereinigungsmengenzeichen
INTERSECT : '\u2229' /*∩*/ | '\\cap'; //(8745)	∩	INTERSECTION	Schnittmengenzeichen
SUBSET    : '\u2282' /*⊂*/ | '\\subset';
SETMINUS  : '\u2216' /*∖*/ | '\\setminus';

DOT_PLUS : '\u2214'; // ∔
MINUS_OR_PLUS: '\u2213'; //∓
ASTERISK: '\u2217';//  ∗
RING: '\u2218'; //∘
CDOT: '\u2219';// ∙
DIVIDES: '\u2223';// (8739)	∣	DIVIDES	teilt
NOT_DIVIDES: '\u2224';// (8740)	∤	DOES NOT DIVIDE	teilt nicht
PARALLEL_TO: '\u2225';//(8741)	∥	PARALLEL TO	parallel zu
NOT_PARALLEL_TO: '\u2226' ;//(8742)	∦	NOT PARALLEL TO	nicht parallel zu
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
ASYMPTOTICALLY_EQUAL_TO: '\u2243' ;// (8771)	≃	ASYMPTOTICALLY EQUAL TO	asymptotisch gleich
NOT_ASYMPTOTICALLY_EQUAL_TO: '\u2244' ;// (8772)	≄	NOT ASYMPTOTICALLY EQUAL TO	nicht asymptotisch gleich

/* MATH PLAN UNICODE
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
/*
U+2980 (10624)	⦀	mathematisches Symbol	TRIPLE VERTICAL BAR DELIMITER	Trennzeichen in Form dreier senkrechter Striche
U+2981 (10625)	⦁	mathematisches Symbol	Z NOTATION SPOT	Punkt der Z-Notation
U+2982 (10626)	⦂	mathematisches Symbol	Z NOTATION TYPE COLON	Doppelpunkt in der Art der Z-Notation
U+2983 (10627)	⦃	öffnende Punktierung
(eines Paars)	LEFT WHITE CURLY BRACKET	Öffnende weiße geschweifte Klammer
U+2984 (10628)	⦄	schließende Punktierung
(eines Paars)	RIGHT WHITE CURLY BRACKET	Schließende weiße geschweifte Klammer
U+2985 (10629)	⦅	öffnende Punktierung
(eines Paars)	LEFT WHITE PARENTHESIS	Öffnende weiße runde Klammer
U+2986 (10630)	⦆	schließende Punktierung
(eines Paars)	RIGHT WHITE PARENTHESIS	Schließende weiße runde Klammer
U+2987 (10631)	⦇	öffnende Punktierung
(eines Paars)	Z NOTATION LEFT IMAGE BRACKET
U+2988 (10632)	⦈	schließende Punktierung
(eines Paars)	Z NOTATION RIGHT IMAGE BRACKET
U+2989 (10633)	⦉	öffnende Punktierung
(eines Paars)	Z NOTATION LEFT BINDING BRACKET
U+298A (10634)	⦊	schließende Punktierung
(eines Paars)	Z NOTATION RIGHT BINDING BRACKET
U+298B (10635)	⦋	öffnende Punktierung
(eines Paars)	LEFT SQUARE BRACKET WITH UNDERBAR	Öffnende eckige Klammer mit Unterstrich
U+298C (10636)	⦌	schließende Punktierung
(eines Paars)	RIGHT SQUARE BRACKET WITH UNDERBAR	Schließende eckige Klammer mit Unterstrich
U+298D (10637)	⦍	öffnende Punktierung
(eines Paars)	LEFT SQUARE BRACKET WITH TICK IN TOP CORNER	Öffnende eckige Klammer mit Strichlein in der oberen Ecke
U+298E (10638)	⦎	schließende Punktierung
(eines Paars)	RIGHT SQUARE BRACKET WITH TICK IN BOTTOM CORNER	Schließende eckige Klammer mit Strichlein in der unteren Ecke
U+298F (10639)	⦏	öffnende Punktierung
(eines Paars)	LEFT SQUARE BRACKET WITH TICK IN BOTTOM CORNER	Öffnende eckige Klammer mit Strichlein in der unteren Ecke
U+2990 (10640)	⦐	schließende Punktierung
(eines Paars)	RIGHT SQUARE BRACKET WITH TICK IN TOP CORNER	Schließende eckige Klammer mit Strichlein in der oberen Ecke
U+2991 (10641)	⦑	öffnende Punktierung
(eines Paars)	LEFT ANGLE BRACKET WITH DOT	Öffnende spitze Klammer mit Punkt
U+2992 (10642)	⦒	schließende Punktierung
(eines Paars)	RIGHT ANGLE BRACKET WITH DOT	Schließende spitze Klammer mit Punkt
U+2993 (10643)	⦓	öffnende Punktierung
(eines Paars)	LEFT ARC LESS-THAN BRACKET
U+2994 (10644)	⦔	schließende Punktierung
(eines Paars)	RIGHT ARC GREATER-THAN BRACKET
U+2995 (10645)	⦕	öffnende Punktierung
(eines Paars)	DOUBLE LEFT ARC GREATER-THAN BRACKET
U+2996 (10646)	⦖	schließende Punktierung
(eines Paars)	DOUBLE RIGHT ARC LESS-THAN BRACKET
U+2997 (10647)	⦗	öffnende Punktierung
(eines Paars)	LEFT BLACK TORTOISE SHELL BRACKET	Öffnende schwarze „Schildkrötenpanzer-Klammer“
U+2998 (10648)	⦘	schließende Punktierung
(eines Paars)	RIGHT BLACK TORTOISE SHELL BRACKET	Schließende schwarze „Schildkrötenpanzer-Klammer“
U+2999 (10649)	⦙	mathematisches Symbol	DOTTED FENCE	Gepunkteter Zaun
U+299A (10650)	⦚	mathematisches Symbol	VERTICAL ZIGZAG LINE	Senkrechte Zickzacklinie
U+299B (10651)	⦛	mathematisches Symbol	MEASURED ANGLE OPENING LEFT	Gerichteter Winkel nach links geöffnet
U+299C (10652)	⦜	mathematisches Symbol	RIGHT ANGLE VARIANT WITH SQUARE	Variante eines rechten Winkels mit Quadrat
U+299D (10653)	⦝	mathematisches Symbol	MEASURED RIGHT ANGLE WITH DOT	Gerichteter rechter Winkel mit Punkt
U+299E (10654)	⦞	mathematisches Symbol	ANGLE WITH S INSIDE	Winkel mit einem S darin
U+299F (10655)	⦟	mathematisches Symbol	ACUTE ANGLE	Spitzer Winkel
U+29A0 (10656)	⦠	mathematisches Symbol	SPHERICAL ANGLE OPENING LEFT	Raumwinkel nach links geöffnet
U+29A1 (10657)	⦡	mathematisches Symbol	SPHERICAL ANGLE OPENING UP	Raumwinkel nach oben geöffnet
U+29A2 (10658)	⦢	mathematisches Symbol	TURNED ANGLE	Gedrehtes Winkelzeichen
U+29A3 (10659)	⦣	mathematisches Symbol	REVERSED ANGLE	Gewendetes Winkelzeichen
U+29A4 (10660)	⦤	mathematisches Symbol	ANGLE WITH UNDERBAR	Winkelzeichen mit Unterstrich
U+29A5 (10661)	⦥	mathematisches Symbol	REVERSED ANGLE WITH UNDERBAR	Gewendetes Winkelzeichen mit Unterstrich
U+29A6 (10662)	⦦	mathematisches Symbol	OBLIQUE ANGLE OPENING UP	Stumpfer Winkel mit Öffnung nach oben
U+29A7 (10663)	⦧	mathematisches Symbol	OBLIQUE ANGLE OPENING DOWN	Stumpfer Winkel mit Öffnung nach unten
U+29A8 (10664)	⦨	mathematisches Symbol	MEASURED ANGLE WITH OPEN ARM ENDING IN ARROW POINTING UP AND RIGHT	Gerichteter Winkel nach rechts geöffnet mit Pfeil nach rechts oben
U+29A9 (10665)	⦩	mathematisches Symbol	MEASURED ANGLE WITH OPEN ARM ENDING IN ARROW POINTING UP AND LEFT	Gerichteter Winkel nach links geöffnet mit Pfeil nach links oben
U+29AA (10666)	⦪	mathematisches Symbol	MEASURED ANGLE WITH OPEN ARM ENDING IN ARROW POINTING DOWN AND RIGHT	Gerichteter Winkel nach rechts geöffnet mit Pfeil nach rechts unten
U+29AB (10667)	⦫	mathematisches Symbol	MEASURED ANGLE WITH OPEN ARM ENDING IN ARROW POINTING DOWN AND LEFT	Gerichteter Winkel nach links geöffnet mit Pfeil nach links unten
U+29AC (10668)	⦬	mathematisches Symbol	MEASURED ANGLE WITH OPEN ARM ENDING IN ARROW POINTING RIGHT AND UP	Gerichteter Winkel nach oben geöffnet mit Pfeil nach rechts oben
U+29AD (10669)	⦭	mathematisches Symbol	MEASURED ANGLE WITH OPEN ARM ENDING IN ARROW POINTING LEFT AND UP	Gerichteter Winkel nach oben geöffnet mit Pfeil nach links oben
U+29AE (10670)	⦮	mathematisches Symbol	MEASURED ANGLE WITH OPEN ARM ENDING IN ARROW POINTING RIGHT AND DOWN	Gerichteter Winkel nach unten geöffnet mit Pfeil nach rechts unten
U+29AF (10671)	⦯	mathematisches Symbol	MEASURED ANGLE WITH OPEN ARM ENDING IN ARROW POINTING LEFT AND DOWN	Gerichteter Winkel nach unten geöffnet mit Pfeil nach links unten
U+29B0 (10672)	⦰	mathematisches Symbol	REVERSED EMPTY SET	Gewendetes Leere-Menge-Zeichen
U+29B1 (10673)	⦱	mathematisches Symbol	EMPTY SET WITH OVERBAR	Leere-Menge-Zeichen mit Überstrich
U+29B2 (10674)	⦲	mathematisches Symbol	EMPTY SET WITH SMALL CIRCLE ABOVE	Leere-Menge-Zeichen mit übergesetztem Kreis
U+29B3 (10675)	⦳	mathematisches Symbol	EMPTY SET WITH RIGHT ARROW ABOVE	Leere-Menge-Zeichen mit übergesetztem Pfeil nach rechts
U+29B4 (10676)	⦴	mathematisches Symbol	EMPTY SET WITH LEFT ARROW ABOVE	Leere-Menge-Zeichen mit übergesetztem Pfeil nach links
U+29B5 (10677)	⦵	mathematisches Symbol	CIRCLE WITH HORIZONTAL BAR	Kreis mit Querstrich
U+29B6 (10678)	⦶	mathematisches Symbol	CIRCLED VERTICAL BAR	Eingekreister senkrechter Strich
U+29B7 (10679)	⦷	mathematisches Symbol	CIRCLED PARALLEL	Eingekreistes Parallel-zu-Zeichen
U+29B8 (10680)	⦸	mathematisches Symbol	CIRCLED REVERSE SOLIDUS	Eingekreister umgekehrter Schrägstrich
U+29B9 (10681)	⦹	mathematisches Symbol	CIRCLED PERPENDICULAR
U+29BA (10682)	⦺	mathematisches Symbol	CIRCLE DIVIDED BY HORIZONTAL BAR AND TOP HALF DIVIDED BY VERTICAL BAR	Kreis geteilt durch einen Querstrich und die obere Hälfte geteilt durch einen senkrechten Strich
U+29BB (10683)	⦻	mathematisches Symbol	CIRCLE WITH SUPERIMPOSED X	Kreis mit darübergelegtem X
U+29BC (10684)	⦼	mathematisches Symbol	CIRCLED ANTICLOCKWISE-ROTATED DIVISION SIGN	Eingekreistes gegen den Uhrzeigersinn gedrehtes Divisionszeichen
U+29BD (10685)	⦽	mathematisches Symbol	UP ARROW THROUGH CIRCLE	Pfeil nach oben durch Kreis hindurch
U+29BE (10686)	⦾	mathematisches Symbol	CIRCLED WHITE BULLET	Eingekreistes weißes Aufzählungszeichen
U+29BF (10687)	⦿	mathematisches Symbol	CIRCLED BULLET	Eingekreistes Aufzählungszeichen
U+29C0 (10688)	⧀	mathematisches Symbol	CIRCLED LESS-THAN	Eingekreistes Kleiner-als-Zeichen
U+29C1 (10689)	⧁	mathematisches Symbol	CIRCLED GREATER-THAN	Eingekreistes Größer-als-Zeichen
U+29C2 (10690)	⧂	mathematisches Symbol	CIRCLE WITH SMALL CIRCLE TO THE RIGHT	Kreis mit kleinem Kreis an der rechten Seite
U+29C3 (10691)	⧃	mathematisches Symbol	CIRCLE WITH TWO HORIZONTAL STROKES TO THE RIGHT	Kreis mit zwei waagerechten Strichen an der rechten Seite
U+29C4 (10692)	⧄	mathematisches Symbol	SQUARED RISING DIAGONAL SLASH	Von einem Quadrat umschlossene steigende Diagonale
U+29C5 (10693)	⧅	mathematisches Symbol	SQUARED FALLING DIAGONAL SLASH	Von einem Quadrat umschlossene fallende Diagonale
U+29C6 (10694)	⧆	mathematisches Symbol	SQUARED ASTERISK	Von einem Quadrat umschlossenes Sternchen
U+29C7 (10695)	⧇	mathematisches Symbol	SQUARED SMALL CIRCLE	Von einem Quadrat umschlossener kleiner Kreis
U+29C8 (10696)	⧈	mathematisches Symbol	SQUARED SQUARE	Von einem Quadrat umschlossenes Quadrat
U+29C9 (10697)	⧉	mathematisches Symbol	TWO JOINED SQUARES	Zwei verbundene Quadrate
U+29CA (10698)	⧊	mathematisches Symbol	TRIANGLE WITH DOT ABOVE	Dreieck mit übergesetztem Punkt
U+29CB (10699)	⧋	mathematisches Symbol	TRIANGLE WITH UNDERBAR	Dreieck mit Unterstrich
U+29CC (10700)	⧌	mathematisches Symbol	S IN TRIANGLE	S in einem Dreieck
U+29CD (10701)	⧍	mathematisches Symbol	TRIANGLE WITH SERIFS AT BOTTOM	Dreieck mit Serifen an der Unterseite
U+29CE (10702)	⧎	mathematisches Symbol	RIGHT TRIANGLE ABOVE LEFT TRIANGLE	Nach rechts zeigendes Dreieck über nach links zeigendem Dreieck
U+29CF (10703)	⧏	mathematisches Symbol	LEFT TRIANGLE BESIDE VERTICAL BAR	Nach links zeigendes Dreieck neben senkrechtem Strich
U+29D0 (10704)	⧐	mathematisches Symbol	VERTICAL BAR BESIDE RIGHT TRIANGLE	Senkrechter Strich neben einem nach rechts zeigenden Dreieck
U+29D1 (10705)	⧑	mathematisches Symbol	BOWTIE WITH LEFT HALF BLACK	Fliege mit schwarzer linker Hälfte
U+29D2 (10706)	⧒	mathematisches Symbol	BOWTIE WITH RIGHT HALF BLACK	Fliege mit schwarzer rechter Hälfte
U+29D3 (10707)	⧓	mathematisches Symbol	BLACK BOWTIE	Schwarze Fliege
U+29D4 (10708)	⧔	mathematisches Symbol	TIMES WITH LEFT HALF BLACK	Malzeichen mit schwarz aufgefüllter linker Hälfte
U+29D5 (10709)	⧕	mathematisches Symbol	TIMES WITH RIGHT HALF BLACK	Malzeichen mit schwarz aufgefüllter rechter Hälfte
U+29D6 (10710)	⧖	mathematisches Symbol	WHITE HOURGLASS	Weiße Sanduhr
U+29D7 (10711)	⧗	mathematisches Symbol	BLACK HOURGLASS	Schwarze Sanduhr
U+29D8 (10712)	⧘	öffnende Punktierung
(eines Paars)	LEFT WIGGLY FENCE	Linker welliger Strich
U+29D9 (10713)	⧙	schließende Punktierung
(eines Paars)	RIGHT WIGGLY FENCE	Rechter welliger Strich
U+29DA (10714)	⧚	öffnende Punktierung
(eines Paars)	LEFT DOUBLE WIGGLY FENCE	Linker doppelter welliger Strich
U+29DB (10715)	⧛	schließende Punktierung
(eines Paars)	RIGHT DOUBLE WIGGLY FENCE	Rechter doppelter welliger Strich
U+29DC (10716)	⧜	mathematisches Symbol	INCOMPLETE INFINITY	Unvollständiges Unendlichkeitszeichen
U+29DD (10717)	⧝	mathematisches Symbol	TIE OVER INFINITY	Bindebogen über Unendlichkeitszeichen
U+29DE (10718)	⧞	mathematisches Symbol	INFINITY NEGATED WITH VERTICAL BAR
U+29DF (10719)	⧟	mathematisches Symbol	DOUBLE-ENDED MULTIMAP	Multimengenzeichen mit zwei Enden
U+29E0 (10720)	⧠	mathematisches Symbol	SQUARE WITH CONTOURED OUTLINE	D’Alembert-Operator
U+29E1 (10721)	⧡	mathematisches Symbol	INCREASES AS
U+29E2 (10722)	⧢	mathematisches Symbol	SHUFFLE PRODUCT	Shuffle-Produkt
U+29E3 (10723)	⧣	mathematisches Symbol	EQUALS SIGN AND SLANTED PARALLEL
U+29E4 (10724)	⧤	mathematisches Symbol	EQUALS SIGN AND SLANTED PARALLEL WITH TILDE ABOVE
U+29E5 (10725)	⧥	mathematisches Symbol	IDENTICAL TO AND SLANTED PARALLEL
U+29E6 (10726)	⧦	mathematisches Symbol	GLEICH STARK	tautologisch äquivalent
U+29E7 (10727)	⧧	mathematisches Symbol	THERMODYNAMIC	Thermodynamisch
U+29E8 (10728)	⧨	mathematisches Symbol	DOWN-POINTING TRIANGLE WITH LEFT HALF BLACK	Nach unten zeigendes Dreieck mit linker schwarzer Hälfte
U+29E9 (10729)	⧩	mathematisches Symbol	DOWN-POINTING TRIANGLE WITH RIGHT HALF BLACK	Nach unten zeigendes Dreieck mit rechter schwarzer Hälfte
U+29EA (10730)	⧪	mathematisches Symbol	BLACK DIAMOND WITH DOWN ARROW	Schwarzes Karo mit Pfeil nach unten
U+29EB (10731)	⧫	mathematisches Symbol	BLACK LOZENGE	Schwarzer Rhombus
U+29EC (10732)	⧬	mathematisches Symbol	WHITE CIRCLE WITH DOWN ARROW	Weißer Kreis mit Pfeil nach unten
U+29ED (10733)	⧭	mathematisches Symbol	BLACK CIRCLE WITH DOWN ARROW	Schwarzer Kreis mit Pfeil nach unten
U+29EE (10734)	⧮	mathematisches Symbol	ERROR-BARRED WHITE SQUARE	Weißes Quadrat mit Fehlerbalken
U+29EF (10735)	⧯	mathematisches Symbol	ERROR-BARRED BLACK SQUARE	Schwarzes Quadrat mit Fehlerbalken
U+29F0 (10736)	⧰	mathematisches Symbol	ERROR-BARRED WHITE DIAMOND	Weißer Rhombus mit Fehlerbalken
U+29F1 (10737)	⧱	mathematisches Symbol	ERROR-BARRED BLACK DIAMOND	Schwarzer Rhombus mit Fehlerbalken
U+29F2 (10738)	⧲	mathematisches Symbol	ERROR-BARRED WHITE CIRCLE	Weißer Kreis mit Fehlerbalken
U+29F3 (10739)	⧳	mathematisches Symbol	ERROR-BARRED BLACK CIRCLE	Schwarzer Kreis mit Fehlerbalken
U+29F4 (10740)	⧴	mathematisches Symbol	RULE-DELAYED
U+29F5 (10741)	⧵	mathematisches Symbol	REVERSE SOLIDUS OPERATOR	Operator umgekehrter Schrägstrich
U+29F6 (10742)	⧶	mathematisches Symbol	SOLIDUS WITH OVERBAR	Schrägstrich mit Überstrich
U+29F7 (10743)	⧷	mathematisches Symbol	REVERSE SOLIDUS WITH HORIZONTAL STROKE	Umgekehrter Schrägstrich mit Querstrich
U+29F8 (10744)	⧸	mathematisches Symbol	BIG SOLIDUS	Großer Schrägstrich
U+29F9 (10745)	⧹	mathematisches Symbol	BIG REVERSE SOLIDUS	Großer umgekehrter Schrägstrich
U+29FA (10746)	⧺	mathematisches Symbol	DOUBLE PLUS	Doppeltes Pluszeichen
U+29FB (10747)	⧻	mathematisches Symbol	TRIPLE PLUS	Dreifaches Pluszeichen
U+29FC (10748)	⧼	öffnende Punktierung
(eines Paars)	LEFT-POINTING CURVED ANGLE BRACKET	Nach links zeigende gekrümmte spitze Klammer
U+29FD (10749)	⧽	schließende Punktierung
(eines Paars)	RIGHT-POINTING CURVED ANGLE BRACKET	Nach rechts zeigende gekrümmte spitze Klammer
U+29FE (10750)	⧾	mathematisches Symbol	TINY	Tiny (Kombinatorische Spieltheorie)
U+29FF (10751)	⧿	mathematisches Symbol	MINY	Miny (Kombinatorische Spieltheorie)
*/
/*
PLAN B
U+2A00 (10752)	⨀	N-ARY CIRCLED DOT OPERATOR	N-stelliger eingekreister Punktoperator
U+2A01 (10753)	⨁	N-ARY CIRCLED PLUS OPERATOR	N-stelliges eingekreistes Pluszeichen
U+2A02 (10754)	⨂	N-ARY CIRCLED TIMES OPERATOR	N-stelliges eingekreistes Multiplikationszeichen
U+2A03 (10755)	⨃	N-ARY UNION OPERATOR WITH DOT	N-stelliges Vereinigungszeichen mit Punkt
U+2A04 (10756)	⨄	N-ARY UNION OPERATOR WITH PLUS	N-stelliges Vereinigungszeichen mit Pluszeichen
U+2A05 (10757)	⨅	N-ARY SQUARE INTERSECTION OPERATOR	N-stelliger viereckiger Schnittmengenoperator
U+2A06 (10758)	⨆	N-ARY SQUARE UNION OPERATOR	N-stelliger viereckiger Vereinigungsmengenoperator
U+2A07 (10759)	⨇	TWO LOGICAL AND OPERATOR	Doppelter logischer UND-Operator
U+2A08 (10760)	⨈	TWO LOGICAL OR OPERATOR	Doppelter logischer ODER-Operator
U+2A09 (10761)	⨉	N-ARY TIMES OPERATOR	N-stelliger Kreuzproduktoperator
U+2A0A (10762)	⨊	MODULO TWO SUM	Summe modulo 2
U+2A0B (10763)	⨋	SUMMATION WITH INTEGRAL	Summenzeichen mit Integral
U+2A0C (10764)	⨌	QUADRUPLE INTEGRAL OPERATOR	Vierfaches Integralzeichen
U+2A0D (10765)	⨍	FINITE PART INTEGRAL
U+2A0E (10766)	⨎	INTEGRAL WITH DOUBLE STROKE
U+2A0F (10767)	⨏	INTEGRAL AVERAGE WITH SLASH
U+2A10 (10768)	⨐	CIRCULATION FUNCTION
U+2A11 (10769)	⨑	ANTICLOCKWISE INTEGRATION
U+2A12 (10770)	⨒	LINE INTEGRATION WITH RECTANGULAR PATH AROUND POLE
U+2A13 (10771)	⨓	LINE INTEGRATION WITH SEMICIRCULAR PATH AROUND POLE
U+2A14 (10772)	⨔	LINE INTEGRATION NOT INCLUDING THE POLE
U+2A15 (10773)	⨕	INTEGRAL AROUND A POINT OPERATOR
U+2A16 (10774)	⨖	QUATERNION INTEGRAL OPERATOR
U+2A17 (10775)	⨗	INTEGRAL WITH LEFTWARDS ARROW WITH HOOK
U+2A18 (10776)	⨘	INTEGRAL WITH TIMES SIGN
U+2A19 (10777)	⨙	INTEGRAL WITH INTERSECTION	Integralzeichen mit Schnittmenge
U+2A1A (10778)	⨚	INTEGRAL WITH UNION	Integralzeichen mit Vereinigungsmenge
U+2A1B (10779)	⨛	INTEGRAL WITH OVERBAR	Integral mit Oberstrich
U+2A1C (10780)	⨜	INTEGRAL WITH UNDERBAR	Integral mit Unterstrich
U+2A1D (10781)	⨝	JOIN	Join-Operator
U+2A1E (10782)	⨞	LARGE LEFT TRIANGLE OPERATOR
U+2A1F (10783)	⨟	Z NOTATION SCHEMA COMPOSITION
U+2A20 (10784)	⨠	Z NOTATION SCHEMA PIPING
U+2A21 (10785)	⨡	Z NOTATION SCHEMA PROJECTION
U+2A22 (10786)	⨢	PLUS SIGN WITH SMALL CIRCLE ABOVE	Pluszeichen mit übergesetztem Ring
U+2A23 (10787)	⨣	PLUS SIGN WITH CIRCUMFLEX ACCENT ABOVE	Pluszeichen mit übergesetztem Zirkumflex
U+2A24 (10788)	⨤	PLUS SIGN WITH TILDE ABOVE	Pluszeichen mit übergesetzter Tilde
U+2A25 (10789)	⨥	PLUS SIGN WITH DOT BELOW	Pluszeichen mit untergesetztem Punkt
U+2A26 (10790)	⨦	PLUS SIGN WITH TILDE BELOW	Pluszeichen mit untergesetzter Tilde
U+2A27 (10791)	⨧	PLUS SIGN WITH SUBSCRIPT TWO	Pluszeichen mit tiefgestellter Ziffer Zwei
U+2A28 (10792)	⨨	PLUS SIGN WITH BLACK TRIANGLE	Pluszeichen mit schwarzem Dreieck
U+2A29 (10793)	⨩	MINUS SIGN WITH COMMA ABOVE	Minuszeichen mit übergesetztem Komma
U+2A2A (10794)	⨪	MINUS SIGN WITH DOT BELOW	Minuszeichen mit untergesetztem Punkt
U+2A2B (10795)	⨫	MINUS SIGN WITH FALLING DOTS	Minuszeichen mit Punkt links oben und rechts unten
U+2A2C (10796)	⨬	MINUS SIGN WITH RISING DOTS	Minuszeichen mit Punkt rechts oben und links unten
U+2A2D (10797)	⨭	PLUS SIGN IN LEFT HALF CIRCLE	Pluszeichen in linksseitigem Halbkreis
U+2A2E (10798)	⨮	PLUS SIGN IN RIGHT HALF CIRCLE	Pluszeichen in rechtsseitigem Halbkreis
U+2A2F (10799)	⨯	VECTOR OR CROSS PRODUCT	Kreuzprodukt
U+2A30 (10800)	⨰	MULTIPLICATION SIGN WITH DOT ABOVE	Multiplikationszeichen (Kreuzprodukt) mit übergesetztem Punkt
U+2A31 (10801)	⨱	MULTIPLICATION SIGN WITH UNDERBAR	Multiplikationszeichen (Kreuzprodukt) mit Unterstrich
U+2A32 (10802)	⨲	SEMIDIRECT PRODUCT WITH BOTTOM CLOSED
U+2A33 (10803)	⨳	SMASH PRODUCT	Smash-Produkt
U+2A34 (10804)	⨴	MULTIPLICATION SIGN IN LEFT HALF CIRCLE	Multiplikationszeichen (Kreuzprodukt) in linksseitigem Halbkreis
U+2A35 (10805)	⨵	MULTIPLICATION SIGN IN RIGHT HALF CIRCLE	Multiplikationszeichen (Kreuzprodukt) in rechtsseitigem Halbkreis
U+2A36 (10806)	⨶	CIRCLED MULTIPLICATION SIGN WITH CIRCUMFLEX ACCENT	Eingekreistes Multiplikationszeichen mit Zirkumflex
U+2A37 (10807)	⨷	MULTIPLICATION SIGN IN DOUBLE CIRCLE	Doppelt eingekreistes Multiplikationszeichen
U+2A38 (10808)	⨸	CIRCLED DIVISION SIGN	Eingekreistes Divisionszeichen
U+2A39 (10809)	⨹	PLUS SIGN IN TRIANGLE	Pluszeichen im Dreieck
U+2A3A (10810)	⨺	MINUS SIGN IN TRIANGLE	Minuszeichen im Dreieck
U+2A3B (10811)	⨻	MULTIPLICATION SIGN IN TRIANGLE	Multiplikationszeichen im Dreieck
U+2A3C (10812)	⨼	INTERIOR PRODUCT	Inneres Produkt
U+2A3D (10813)	⨽	RIGHTHAND INTERIOR PRODUCT	Rechtsseitiges inneres Produkt
U+2A3E (10814)	⨾	Z NOTATION RELATIONAL COMPOSITION
U+2A3F (10815)	⨿	AMALGAMATION OR COPRODUCT	Koprodukt
U+2A40 (10816)	⩀	INTERSECTION WITH DOT	Schnittmengenzeichen mit Punkt
U+2A41 (10817)	⩁	UNION WITH MINUS SIGN	Vereinigungsmengenzeichen mit Minuszeichen
U+2A42 (10818)	⩂	UNION WITH OVERBAR	Vereinigungsmengenzeichen mit übergesetztem Makron
U+2A43 (10819)	⩃	INTERSECTION WITH OVERBAR	Schnittmengenzeichen mit übergesetztem Makron
U+2A44 (10820)	⩄	INTERSECTION WITH LOGICAL AND	Schnittmengenzeichen mit logischem UND
U+2A45 (10821)	⩅	UNION WITH LOGICAL OR	Vereinigungsmengenzeichen mit logischem ODER
U+2A46 (10822)	⩆	UNION ABOVE INTERSECTION	Vereinigungsmengenzeichen über Schnittmengenzeichen
U+2A47 (10823)	⩇	INTERSECTION ABOVE UNION	Schnittmengenzeichen über Vereinigungsmengenzeichen
U+2A48 (10824)	⩈	UNION ABOVE BAR ABOVE INTERSECTION	Vereinigungsmengenzeichen über horizontalem Strich und Schnittmengenzeichen
U+2A49 (10825)	⩉	INTERSECTION ABOVE BAR ABOVE UNION	Schnittmengenzeichen über horizontalem Strich und Vereinigungsmengenzeichen
U+2A4A (10826)	⩊	UNION BESIDE AND JOINED WITH UNION
U+2A4B (10827)	⩋	INTERSECTION BESIDE AND JOINED WITH INTERSECTION
U+2A4C (10828)	⩌	CLOSED UNION WITH SERIFS	Geschlossenes Vereinigungsmengenzeichen mit Serifen
U+2A4D (10829)	⩍	CLOSED INTERSECTION WITH SERIFS	Geschlossenes Schnittmengenzeichen mit Serifen
U+2A4E (10830)	⩎	DOUBLE SQUARE INTERSECTION	Doppeltes eckiges Schnittmengenzeichen
U+2A4F (10831)	⩏	DOUBLE SQUARE UNION	Doppeltes eckiges Vereinigungsmengenzeichen
U+2A50 (10832)	⩐	CLOSED UNION WITH SERIFS AND SMASH PRODUCT	Geschlossenes Vereinigungsmengenzeichen mit Serifen und Smash-Produkt
U+2A51 (10833)	⩑	LOGICAL AND WITH DOT ABOVE	Logisches UND mit übergesetztem Punkt
U+2A52 (10834)	⩒	LOGICAL OR WITH DOT ABOVE	Logisches ODER mit übergesetztem Punkt
U+2A53 (10835)	⩓	DOUBLE LOGICAL AND	Doppeltes logisches UND
U+2A54 (10836)	⩔	DOUBLE LOGICAL OR	Doppeltes logisches ODER
U+2A55 (10837)	⩕	TWO INTERSECTING LOGICAL AND	Zwei sich überschneidende logische UND-Operatoren
U+2A56 (10838)	⩖	TWO INTERSECTING LOGICAL OR	Zwei sich überschneidende logische ODER-Operatoren
U+2A57 (10839)	⩗	SLOPING LARGE OR	Schräges logisches Oder
U+2A58 (10840)	⩘	SLOPING LARGE AND	Schräges logisches Und
U+2A59 (10841)	⩙	LOGICAL OR OVERLAPPING LOGICAL AND	Sich mit logischem Und überschneidendes logisches Oder
U+2A5A (10842)	⩚	LOGICAL AND WITH MIDDLE STEM	Logisches UND mit Mittelstrich
U+2A5B (10843)	⩛	LOGICAL OR WITH MIDDLE STEM	Logisches ODER mit Mittelstrich
U+2A5C (10844)	⩜	LOGICAL AND WITH HORIZONTAL DASH	Durchgestrichenes logisches Und
U+2A5D (10845)	⩝	LOGICAL OR WITH HORIZONTAL DASH	Durchgestrichenes logisches Oder
U+2A5E (10846)	⩞	LOGICAL AND WITH DOUBLE OVERBAR	Logisches Und mit übergesetztem doppeltem Makron
U+2A5F (10847)	⩟	LOGICAL AND WITH UNDERBAR	Logisches Und mit Unterstrich
U+2A60 (10848)	⩠	LOGICAL AND WITH DOUBLE UNDERBAR	Logisches Und mit doppeltem Unterstrich
U+2A61 (10849)	⩡	SMALL VEE WITH UNDERBAR	Lateinischer Kleinbuchstabe V mit Unterstrich
U+2A62 (10850)	⩢	LOGICAL OR WITH DOUBLE OVERBAR	Logisches Oder mit übergesetztem doppeltem Makron
U+2A63 (10851)	⩣	LOGICAL OR WITH DOUBLE UNDERBAR	Logisches Oder mit doppeltem Unterstrich
U+2A64 (10852)	⩤	Z NOTATION DOMAIN ANTIRESTRICTION
U+2A65 (10853)	⩥	Z NOTATION RANGE ANTIRESTRICTION
U+2A66 (10854)	⩦	EQUALS SIGN WITH DOT BELOW	Gleichheitszeichen mit untergesetztem Punkt
U+2A67 (10855)	⩧	IDENTICAL WITH DOT ABOVE	Kongruenzzeichen mit übergesetztem Punkt
U+2A68 (10856)	⩨	TRIPLE HORIZONTAL BAR WITH DOUBLE VERTICAL STROKE	Doppelt durchgestrichenes Kongruenzzeichen
U+2A69 (10857)	⩩	TRIPLE HORIZONTAL BAR WITH TRIPLE VERTICAL STROKE	Dreifach durchgestrichenes Kongruenzzeichen
U+2A6A (10858)	⩪	TILDE OPERATOR WITH DOT ABOVE	Tildeoperator mit übergesetztem Punkt
U+2A6B (10859)	⩫	TILDE OPERATOR WITH RISING DOTS	Tildeoperator mit Punkt rechts oben und links unten
U+2A6C (10860)	⩬	SIMILAR MINUS SIMILAR	Tilde über Minuszeichen und Tilde
U+2A6D (10861)	⩭	CONGRUENT WITH DOT ABOVE	Ungefähr-gleich-Zeichen mit übergesetztem Punkt
U+2A6E (10862)	⩮	EQUALS WITH ASTERISK	Gleichheitszeichen mit übergesetztem Stern
U+2A6F (10863)	⩯	ALMOST EQUAL TO WITH CIRCUMFLEX ACCENT	Fast-gleich-Zeichen mit übergesetztem Zirkumflex
U+2A70 (10864)	⩰	APPROXIMATELY EQUAL OR EQUAL TO	fast gleich oder gleich
U+2A71 (10865)	⩱	EQUALS SIGN ABOVE PLUS SIGN	Gleichheitszeichen über Pluszeichen
U+2A72 (10866)	⩲	PLUS SIGN ABOVE EQUALS SIGN	Pluszeichen über Gleichheitszeichen
U+2A73 (10867)	⩳	EQUALS SIGN ABOVE TILDE OPERATOR	Gleichheitszeichen über Tildeoperator
U+2A74 (10868)	⩴	DOUBLE COLON EQUAL	Zwei Doppelpunkte und Gleichheitszeichen
U+2A75 (10869)	⩵	TWO CONSECUTIVE EQUALS SIGNS	Zwei Gleichheitszeichen
U+2A76 (10870)	⩶	THREE CONSECUTIVE EQUALS SIGNS	Drei Gleichheitszeichen
U+2A77 (10871)	⩷	EQUALS SIGN WITH TWO DOTS ABOVE AND TWO DOTS BELOW	Gleichheitszeichen mit übergesetztem und untergesetztem Trema
U+2A78 (10872)	⩸	EQUIVALENT WITH FOUR DOTS ABOVE	Äquivalenzzeichen mit vier übergesetzten Punkten
U+2A79 (10873)	⩹	LESS-THAN WITH CIRCLE INSIDE	Kleiner-als-Zeichen mit Ring
U+2A7A (10874)	⩺	GREATER-THAN WITH CIRCLE INSIDE	Größer-als-Zeichen mit Ring
U+2A7B (10875)	⩻	LESS-THAN WITH QUESTION MARK ABOVE	Kleiner-als-Zeichen mit übergesetztem Fragezeichen
U+2A7C (10876)	⩼	GREATER-THAN WITH QUESTION MARK ABOVE	Größer-als-Zeichen mit übergesetztem Fragezeichen
U+2A7D (10877)	⩽	LESS-THAN OR SLANTED EQUAL TO	Schräges Kleiner-als oder gleich
U+2A7E (10878)	⩾	GREATER-THAN OR SLANTED EQUAL TO	Schräges Größer-als oder gleich
U+2A7F (10879)	⩿	LESS-THAN OR SLANTED EQUAL TO WITH DOT INSIDE	Schräges Kleiner-als oder gleich mit Punkt
U+2A80 (10880)	⪀	GREATER-THAN OR SLANTED EQUAL TO WITH DOT INSIDE	Schräges Größer-als oder gleich mit Punkt
U+2A81 (10881)	⪁	LESS-THAN OR SLANTED EQUAL TO WITH DOT ABOVE	Schräges Kleiner-als oder gleich mit übergesetztem Punkt
U+2A82 (10882)	⪂	GREATER-THAN OR SLANTED EQUAL TO WITH DOT ABOVE	Schräges Größer-als oder gleich mit übergesetztem Punkt
U+2A83 (10883)	⪃	LESS-THAN OR SLANTED EQUAL TO WITH DOT ABOVE RIGHT	Schräges Kleiner-als oder gleich mit Punkt rechts oben
U+2A84 (10884)	⪄	GREATER-THAN OR SLANTED EQUAL TO WITH DOT ABOVE LEFT	Schräges Größer-als oder gleich mit Punkt links oben
U+2A85 (10885)	⪅	LESS-THAN OR APPROXIMATE	Kleiner oder ungefähr gleich
U+2A86 (10886)	⪆	GREATER-THAN OR APPROXIMATE	Größer oder ungefähr gleich
U+2A87 (10887)	⪇	LESS-THAN AND SINGLE-LINE NOT EQUAL TO	Kleiner und nicht gleich
U+2A88 (10888)	⪈	GREATER-THAN AND SINGLE-LINE NOT EQUAL TO	Größer und nicht gleich
U+2A89 (10889)	⪉	LESS-THAN AND NOT APPROXIMATE	Echt kleiner und nicht ungefähr gleich
U+2A8A (10890)	⪊	GREATER-THAN AND NOT APPROXIMATE	Echt größer und nicht ungefähr gleich
U+2A8B (10891)	⪋	LESS-THAN ABOVE DOUBLE-LINE EQUAL ABOVE GREATER-THAN	Kleiner-als über Gleichheitszeichen über Größer-als
U+2A8C (10892)	⪌	GREATER-THAN ABOVE DOUBLE-LINE EQUAL ABOVE LESS-THAN	Größer-als über Gleichheitszeichen über Kleiner-als
U+2A8D (10893)	⪍	LESS-THAN ABOVE SIMILAR OR EQUAL	Kleiner als oder gleich oder ungefähr
U+2A8E (10894)	⪎	GREATER-THAN ABOVE SIMILAR OR EQUAL	Größer als oder gleich oder ungefähr
U+2A8F (10895)	⪏	LESS-THAN ABOVE SIMILAR ABOVE GREATER-THAN	Kleiner-als über ungefähr über Größer-als
U+2A90 (10896)	⪐	GREATER-THAN ABOVE SIMILAR ABOVE LESS-THAN	Größer-als über ungefähr über Kleiner-als
U+2A91 (10897)	⪑	LESS-THAN ABOVE GREATER-THAN ABOVE DOUBLE-LINE EQUAL	Kleiner-als über Größer-als über Gleichheitszeichen
U+2A92 (10898)	⪒	GREATER-THAN ABOVE LESS-THAN ABOVE DOUBLE-LINE EQUAL	Größer-als über Kleiner-als über Gleichheitszeichen
U+2A93 (10899)	⪓	LESS-THAN ABOVE SLANTED EQUAL ABOVE GREATER-THAN ABOVE SLANTED EQUAL
U+2A94 (10900)	⪔	GREATER-THAN ABOVE SLANTED EQUAL ABOVE LESS-THAN ABOVE SLANTED EQUAL
U+2A95 (10901)	⪕	SLANTED EQUAL TO OR LESS-THAN
U+2A96 (10902)	⪖	SLANTED EQUAL TO OR GREATER-THAN
U+2A97 (10903)	⪗	SLANTED EQUAL TO OR LESS-THAN WITH DOT INSIDE
U+2A98 (10904)	⪘	SLANTED EQUAL TO OR GREATER-THAN WITH DOT INSIDE
U+2A99 (10905)	⪙	DOUBLE-LINE EQUAL TO OR LESS-THAN
U+2A9A (10906)	⪚	DOUBLE-LINE EQUAL TO OR GREATER-THAN
U+2A9B (10907)	⪛	DOUBLE-LINE SLANTED EQUAL TO OR LESS-THAN
U+2A9C (10908)	⪜	DOUBLE-LINE SLANTED EQUAL TO OR GREATER-THAN
U+2A9D (10909)	⪝	SIMILAR OR LESS-THAN	Ungefähr oder kleiner als
U+2A9E (10910)	⪞	SIMILAR OR GREATER-THAN	Ungefähr oder größer als
U+2A9F (10911)	⪟	SIMILAR ABOVE LESS-THAN ABOVE EQUALS SIGN
U+2AA0 (10912)	⪠	SIMILAR ABOVE GREATER-THAN ABOVE EQUALS SIGN
U+2AA1 (10913)	⪡	DOUBLE NESTED LESS-THAN	Doppeltes geschachteltes Kleiner-als
U+2AA2 (10914)	⪢	DOUBLE NESTED GREATER-THAN	Doppeltes geschachteltes Größer-als
U+2AA3 (10915)	⪣	DOUBLE NESTED LESS-THAN WITH UNDERBAR	Doppeltes geschachteltes Kleiner-als mit Unterstrich
U+2AA4 (10916)	⪤	GREATER-THAN OVERLAPPING LESS-THAN	Größer-als und Kleiner-als überlappend
U+2AA5 (10917)	⪥	GREATER-THAN BESIDE LESS-THAN	Größer-als und Kleiner-als nebeneinander
U+2AA6 (10918)	⪦	LESS-THAN CLOSED BY CURVE
U+2AA7 (10919)	⪧	GREATER-THAN CLOSED BY CURVE
U+2AA8 (10920)	⪨	LESS-THAN CLOSED BY CURVE ABOVE SLANTED EQUAL
U+2AA9 (10921)	⪩	GREATER-THAN CLOSED BY CURVE ABOVE SLANTED EQUAL
U+2AAA (10922)	⪪	SMALLER THAN
U+2AAB (10923)	⪫	LARGER THAN
U+2AAC (10924)	⪬	SMALLER THAN OR EQUAL TO
U+2AAD (10925)	⪭	LARGER THAN OR EQUAL TO
U+2AAE (10926)	⪮	EQUALS SIGN WITH BUMPY ABOVE
U+2AAF (10927)	⪯	PRECEDES ABOVE SINGLE-LINE EQUALS SIGN	Vorgänger oder gleich
U+2AB0 (10928)	⪰	SUCCEEDS ABOVE SINGLE-LINE EQUALS SIGN	Nachfolger oder gleich
U+2AB1 (10929)	⪱	PRECEDES ABOVE SINGLE-LINE NOT EQUAL TO	Vorgänger und nicht gleich
U+2AB2 (10930)	⪲	SUCCEEDS ABOVE SINGLE-LINE NOT EQUAL TO	Nachfolger und nicht gleich
U+2AB3 (10931)	⪳	PRECEDES ABOVE EQUALS SIGN
U+2AB4 (10932)	⪴	SUCCEEDS ABOVE EQUALS SIGN
U+2AB5 (10933)	⪵	PRECEDES ABOVE NOT EQUAL TO
U+2AB6 (10934)	⪶	SUCCEEDS ABOVE NOT EQUAL TO
U+2AB7 (10935)	⪷	PRECEDES ABOVE ALMOST EQUAL TO	Vorgänger oder ungefähr
U+2AB8 (10936)	⪸	SUCCEEDS ABOVE ALMOST EQUAL TO	Nachfolger oder ungefähr
U+2AB9 (10937)	⪹	PRECEDES ABOVE NOT ALMOST EQUAL TO	Vorgänger und nicht ungefähr
U+2ABA (10938)	⪺	SUCCEEDS ABOVE NOT ALMOST EQUAL TO	Nachfolger und nicht ungefähr
U+2ABB (10939)	⪻	DOUBLE PRECEDES	Doppeltes Vorgänger-Zeichen
U+2ABC (10940)	⪼	DOUBLE SUCCEEDS	Doppeltes Nachfolger-Zeichen
U+2ABD (10941)	⪽	SUBSET WITH DOT	Teilmenge mit innenliegendem Punkt
U+2ABE (10942)	⪾	SUPERSET WITH DOT	Obermenge mit innenliegendem Punkt
U+2ABF (10943)	⪿	SUBSET WITH PLUS SIGN BELOW	Teilmenge mit darunterliegendem Pluszeichen
U+2AC0 (10944)	⫀	SUPERSET WITH PLUS SIGN BELOW	Obermenge mit darunterliegendem Pluszeichen
U+2AC1 (10945)	⫁	SUBSET WITH MULTIPLICATION SIGN BELOW	Teilmenge mit darunterliegendem Multiplikationszeichen (Kreuzprodukt)
U+2AC2 (10946)	⫂	SUPERSET WITH MULTIPLICATION SIGN BELOW	Obermenge mit darunterliegendem Multiplikationszeichen (Kreuzprodukt)
U+2AC3 (10947)	⫃	SUBSET OF OR EQUAL TO WITH DOT ABOVE	Teilmenge oder gleich mit darüberliegendem Punkt
U+2AC4 (10948)	⫄	SUPERSET OF OR EQUAL TO WITH DOT ABOVE	Obermenge oder gleich mit darüberliegendem Punkt
U+2AC5 (10949)	⫅	SUBSET OF ABOVE EQUALS SIGN	Teilmenge mit darunterliegendem Gleichheitszeichen
U+2AC6 (10950)	⫆	SUPERSET OF ABOVE EQUALS SIGN	Obermenge mit darunterliegendem Gleichheitszeichen
U+2AC7 (10951)	⫇	SUBSET OF ABOVE TILDE OPERATOR	Teilmenge mit darunterliegender Tilde
U+2AC8 (10952)	⫈	SUPERSET OF ABOVE TILDE OPERATOR	Obermenge mit darunterliegender Tilde
U+2AC9 (10953)	⫉	SUBSET OF ABOVE ALMOST EQUAL TO	Teilmenge mit darunterliegendem Ungefähr-gleich-Zeichen
U+2ACA (10954)	⫊	SUPERSET OF ABOVE ALMOST EQUAL TO	Obermenge mit darunterliegendem Ungefähr-gleich-Zeichen
U+2ACB (10955)	⫋	SUBSET OF ABOVE NOT EQUAL TO	Echte Teilmenge
U+2ACC (10956)	⫌	SUPERSET OF ABOVE NOT EQUAL TO	Echte Obermenge
U+2ACD (10957)	⫍	SQUARE LEFT OPEN BOX OPERATOR
U+2ACE (10958)	⫎	SQUARE RIGHT OPEN BOX OPERATOR
U+2ACF (10959)	⫏	CLOSED SUBSET	Geschlossenes Teilmengenzeichen
U+2AD0 (10960)	⫐	CLOSED SUPERSET	Geschlossenes Obermengenzeichen
U+2AD1 (10961)	⫑	CLOSED SUBSET OR EQUAL TO	Geschlossenes echtes Teilmengenzeichen
U+2AD2 (10962)	⫒	CLOSED SUPERSET OR EQUAL TO	Geschlossenes echtes Obermengenzeichen
U+2AD3 (10963)	⫓	SUBSET ABOVE SUPERSET	Teilmengenzeichen über Obermengenzeichen
U+2AD4 (10964)	⫔	SUPERSET ABOVE SUBSET	Obermengenzeichen über Teilmengenzeichen
U+2AD5 (10965)	⫕	SUBSET ABOVE SUBSET	Zwei Teilmengenzeichen übereinander
U+2AD6 (10966)	⫖	SUPERSET ABOVE SUPERSET	Zwei Obermengenzeichen übereinander
U+2AD7 (10967)	⫗	SUPERSET BESIDE SUBSET	Obermengenzeichen und Teilmengenzeichen nebeneinander
U+2AD8 (10968)	⫘	SUPERSET BESIDE AND JOINED BY DASH WITH SUBSET
U+2AD9 (10969)	⫙	ELEMENT OF OPENING DOWNWARDS	Ist-Element-von mit Öffnung nach unten
U+2ADA (10970)	⫚	PITCHFORK WITH TEE TOP
U+2ADB (10971)	⫛	TRANSVERSAL INTERSECTION
U+2ADC (10972)	⫝̸	FORKING
U+2ADD (10973)	⫝	NONFORKING
U+2ADE (10974)	⫞	SHORT LEFT TACK
U+2ADF (10975)	⫟	SHORT DOWN TACK
U+2AE0 (10976)	⫠	SHORT UP TACK
U+2AE1 (10977)	⫡	PERPENDICULAR WITH S
U+2AE2 (10978)	⫢	VERTICAL BAR TRIPLE RIGHT TURNSTILE
U+2AE3 (10979)	⫣	DOUBLE VERTICAL BAR LEFT TURNSTILE
U+2AE4 (10980)	⫤	VERTICAL BAR DOUBLE LEFT TURNSTILE
U+2AE5 (10981)	⫥	DOUBLE VERTICAL BAR DOUBLE LEFT TURNSTILE
U+2AE6 (10982)	⫦	LONG DASH FROM LEFT MEMBER OF DOUBLE VERTICAL
U+2AE7 (10983)	⫧	SHORT DOWN TACK WITH OVERBAR
U+2AE8 (10984)	⫨	SHORT UP TACK WITH UNDERBAR
U+2AE9 (10985)	⫩	SHORT UP TACK ABOVE SHORT DOWN TACK
U+2AEA (10986)	⫪	DOUBLE DOWN TACK
U+2AEB (10987)	⫫	DOUBLE UP TACK	Stochastische Unabhängigkeit
U+2AEC (10988)	⫬	DOUBLE STROKE NOT SIGN
U+2AED (10989)	⫭	REVERSED DOUBLE STROKE NOT SIGN
U+2AEE (10990)	⫮	DOES NOT DIVIDE WITH REVERSED NEGATION SLASH	Ist-nicht-Teiler-von mit umgedrehtem Negationsschrägstrich
U+2AEF (10991)	⫯	VERTICAL LINE WITH CIRCLE ABOVE
U+2AF0 (10992)	⫰	VERTICAL LINE WITH CIRCLE BELOW
U+2AF1 (10993)	⫱	DOWN TACK WITH CIRCLE BELOW
U+2AF2 (10994)	⫲	PARALLEL WITH HORIZONTAL STROKE
U+2AF3 (10995)	⫳	PARALLEL WITH TILDE OPERATOR
U+2AF4 (10996)	⫴	TRIPLE VERTICAL BAR BINARY RELATION
U+2AF5 (10997)	⫵	TRIPLE VERTICAL BAR WITH HORIZONTAL STROKE
U+2AF6 (10998)	⫶	TRIPLE COLON OPERATOR
U+2AF7 (10999)	⫷	TRIPLE NESTED LESS-THAN	Dreifaches geschachteltes kleiner-als
U+2AF8 (11000)	⫸	TRIPLE NESTED GREATER-THAN	Dreifaches geschachteltes größer-als
U+2AF9 (11001)	⫹	DOUBLE-LINE SLANTED LESS-THAN OR EQUAL TO
U+2AFA (11002)	⫺	DOUBLE-LINE SLANTED GREATER-THAN OR EQUAL TO
U+2AFB (11003)	⫻	TRIPLE SOLIDUS BINARY RELATION	Dreifacher Schrägstrich
U+2AFC (11004)	⫼	LARGE TRIPLE VERTICAL BAR OPERATOR
U+2AFD (11005)	⫽	DOUBLE SOLIDUS OPERATOR	Doppelter Schrägstrich
U+2AFE (11006)	⫾	WHITE VERTICAL BAR	Hohler vertikaler Balken (Dijkstra-Notation)
U+2AFF (11007)	⫿	N-ARY WHITE VERTICAL BAR	N-stufiger hohler vertikaler Balken (Dijkstra-Notation)
*/
/* PLAN A
U+27C0 (10176)	⟀	mathematisches Symbol	THREE DIMENSIONAL ANGLE	Dreidimensionaler Winkel
U+27C1 (10177)	⟁	mathematisches Symbol	WHITE TRIANGLE CONTAINING SMALL WHITE TRIANGLE	Weißes Dreieck in einem weißen Dreieck
U+27C2 (10178)	⟂	mathematisches Symbol	PERPENDICULAR	ist orthogonal zu
U+27C3 (10179)	⟃	mathematisches Symbol	OPEN SUBSET	Offene Teilmenge
U+27C4 (10180)	⟄	mathematisches Symbol	OPEN SUPERSET	Offene Obermenge
U+27C5 (10181)	⟅	öffnende Punktierung    (eines Paars)	LEFT S-SHAPED BAG DELIMITER	Linkes s-förmiges Trennzeichen für Multimengen
U+27C6 (10182)	⟆	schließende Punktierung (eines Paars)	RIGHT S-SHAPED BAG DELIMITER	Rechtes s-förmiges Trennzeichen für Multimengen
U+27C7 (10183)	⟇	mathematisches Symbol	OR WITH DOT INSIDE	Logisches Oder mit Punkt
U+27C8 (10184)	⟈	mathematisches Symbol	REVERSE SOLIDUS PRECEDING SUBSET	Umgekehrter Schrägstrich gefolgt von Teilmenge
U+27C9 (10185)	⟉	mathematisches Symbol	SUPERSET PRECEDING SOLIDUS	Obermenge gefolgt von einem Schrägstrich
U+27CA (10186)	⟊	mathematisches Symbol	VERTICAL BAR WITH HORIZONTAL STROKE	Senkrechter Strich mit Querstrich
U+27CB (10187)	⟋	mathematisches Symbol	MATHEMATICAL RISING DIAGONAL	Mathematische steigende Diagonale
U+27CC (10188)	⟌	mathematisches Symbol	LONG DIVISION	Langes Divisionszeichen
U+27CD (10189)	⟍	mathematisches Symbol	MATHEMATICAL FALLING DIAGONAL	Mathematische fallende Diagonale
U+27CE (10190)	⟎	mathematisches Symbol	SQUARED LOGICAL AND	Logisches Und im Quadrat
U+27CF (10191)	⟏	mathematisches Symbol	SQUARED LOGICAL OR	Logisches Oder im Quadrat
U+27D0 (10192)	⟐	mathematisches Symbol	WHITE DIAMOND WITH CENTRED DOT	Weißes Karo mit Punkt in der Mitte
U+27D1 (10193)	⟑	mathematisches Symbol	AND WITH DOT	Logisches Und mit Punkt
U+27D2 (10194)	⟒	mathematisches Symbol	ELEMENT OF OPENING UPWARDS	Nach oben zeigendes Elementzeichen
U+27D3 (10195)	⟓	mathematisches Symbol	LOWER RIGHT CORNER WITH DOT	Untere rechte Ecke mit Punkt
U+27D4 (10196)	⟔	mathematisches Symbol	UPPER LEFT CORNER WITH DOT	Obere rechte Ecke mit Punkt
U+27D5 (10197)	⟕	mathematisches Symbol	LEFT OUTER JOIN	Linker äußerer Verbund
U+27D6 (10198)	⟖	mathematisches Symbol	RIGHT OUTER JOIN	Rechter äußerer Verbund
U+27D7 (10199)	⟗	mathematisches Symbol	FULL OUTER JOIN	Voller äußerer Verbund
U+27D8 (10200)	⟘	mathematisches Symbol	LARGE UP TACK	Große nach oben zeigende Reißzwecke
U+27D9 (10201)	⟙	mathematisches Symbol	LARGE DOWN TACK	Große nach unten zeigende Reißzwecke
U+27DA (10202)	⟚	mathematisches Symbol	LEFT AND RIGHT DOUBLE TURNSTILE	Linkes und rechtes doppeltes Drehkreuz
U+27DB (10203)	⟛	mathematisches Symbol	LEFT AND RIGHT TACK	Nach links und nach rechts zeigende Reißzwecke
U+27DC (10204)	⟜	mathematisches Symbol	LEFT MULTIMAP	Linke Mehrfachzuordnung
U+27DD (10205)	⟝	mathematisches Symbol	LONG RIGHT TACK	Lange nach rechts zeigende Reißzwecke
U+27DE (10206)	⟞	mathematisches Symbol	LONG LEFT TACK	Lange nach links zeigende Reißzwecke
U+27DF (10207)	⟟	mathematisches Symbol	UP TACK WITH CIRCLE ABOVE	Nach oben zeigende Reißzwecke mit übergesetztem Kreis
U+27E0 (10208)	⟠	mathematisches Symbol	LOZENGE DIVIDED BY HORIZONTAL RULE	Durch horizontale Linie geteilter Rhombus
U+27E1 (10209)	⟡	mathematisches Symbol	WHITE CONCAVE-SIDED DIAMOND	Weißes Karo mit konkaven Seiten
U+27E2 (10210)	⟢	mathematisches Symbol	WHITE CONCAVE-SIDED DIAMOND WITH LEFTWARDS TICK	Weißes Karo mit konkaven Seiten mit nach links zeigendem Strichlein
U+27E3 (10211)	⟣	mathematisches Symbol	WHITE CONCAVE-SIDED DIAMOND WITH RIGHTWARDS TICK	Weißes Karo mit konkaven Seiten mit nach rechts zeigendem Strichlein
U+27E4 (10212)	⟤	mathematisches Symbol	WHITE SQUARE WITH LEFTWARDS TICK	Weißes Quadrat mit nach links zeigendem Strichlein
U+27E5 (10213)	⟥	mathematisches Symbol	WHITE SQUARE WITH RIGHTWARDS TICK	Weißes Quadrat mit nach rechts zeigendem Strichlein
U+27E6 (10214)	⟦	öffnende Punktierung (eines Paars)	MATHEMATICAL LEFT WHITE SQUARE BRACKET	Mathematische öffnende weiße eckige Klammer
U+27E7 (10215)	⟧	schließende Punktierung (eines Paars)	MATHEMATICAL RIGHT WHITE SQUARE BRACKET	Mathematische schließende weiße eckige Klammer
U+27E8 (10216)	⟨	öffnende Punktierung (eines Paars)	MATHEMATICAL LEFT ANGLE BRACKET	Mathematische öffnende spitze Klammer
U+27E9 (10217)	⟩	schließende Punktierung (eines Paars)	MATHEMATICAL RIGHT ANGLE BRACKET	Mathematische schließende spitze Klammer
U+27EA (10218)	⟪	öffnende Punktierung (eines Paars)	MATHEMATICAL LEFT DOUBLE ANGLE BRACKET	Mathematische öffnende doppelte spitze Klammer
U+27EB (10219)	⟫	schließende Punktierung (eines Paars)	MATHEMATICAL RIGHT DOUBLE ANGLE BRACKET	Mathematische schließende doppelte spitze Klammer
U+27EC (10220)	⟬	öffnende Punktierung (eines Paars)	MATHEMATICAL LEFT WHITE TORTOISE SHELL BRACKET	Mathematische öffnende hohle stumpfe Klammer
U+27ED (10221)	⟭	schließende Punktierung (eines Paars)	MATHEMATICAL RIGHT WHITE TORTOISE SHELL BRACKET	Mathematische schließende hohle stumpfe Klammer
U+27EE (10222)	⟮	öffnende Punktierung (eines Paars)	MATHEMATICAL LEFT FLATTENED PARENTHESIS	Mathematische öffnende abgeflachte runde Klammer
U+27EF (10223)	⟯	schließende Punktierung (eines Paars)	MATHEMATICAL RIGHT FLATTENED PARENTHESIS	Mathematische schließende abgeflachte runde Klammer
*/

SEQARROW    : '==>' | '\u27F9';
NOT_EQUALS  : '!=' OP_SFX* | '\u2260';
APPROXIMATELY_BUT_NOT_ACTUALLY_EQUAL_TO     : '\u2246'; // (8774)	≆	APPROXIMATELY BUT NOT ACTUALLY EQUAL TO	ungefähr, aber nicht genau gleich
NEITHER_APPROXIMATELY_NOR_ACTUALLY_EQUAL_TO : '\u2247'; // (8775)	≇	NEITHER APPROXIMATELY NOR ACTUALLY EQUAL TO	weder ungefähr noch genau gleich
NOT_IDENTICAL_TO    : '\u2262'; // (8802)	≢	NOT IDENTICAL TO	ist nicht kongruent zu

IMP         : '->' | '\u2192';
AT          : '@' OP_SFX*;
OR          : '|' OP_SFX? | '\u2228';
SQUARE_CUP  : '\u2294' | '\\sqcup'; // (8852)	⊔	SQUARE CUP	nach oben geöffnetes Viereck

AND         : '&' OP_SFX? | '\u2227';
SQUARE_CAP  : '\u2293' | '\\sqcap'; // (8851)	⊓	SQUARE CAP	nach unten geöffnetes Viereck


NOT             : '!' (OP_SFX|'!')? | '\u00AC';
EQUALS          : '=' OP_SFX?;
IDENTICAL_TO    : '\u2261' | '\\equiv'; // (8801)	≡	IDENTICAL TO	ist kongruent zu
CIRCLED_EQUALS  : '\u229C'; // (8860)	⊜	CIRCLED EQUALS	eingekreistes Gleichheitszeichen

EXP         : '^' OP_SFX?;
TILDE       : ('~'|'\u223C') OP_SFX?;


SLASH                   : '/' OP_SFX*;
CIRCLED_DIVISION_SLASH  : '\u2298'; // (8856)	⊘	CIRCLED DIVISION SLASH	eingekreister Divisionsstrich


PERCENT                 : '%' OP_SFX?;
CIRCLED_RING_OPERATOR   :   '\u229A'; // (8858)	⊚	CIRCLED RING OPERATOR	eingekreister Ringoperator

STAR                        : '*' OP_SFX?;
CIRCLED_TIMES               : '\u2297'; // (8855)	⊗	CIRCLED TIMES	eingekreistes Multiplikationszeichen
CIRCLED_DOT_OPERATOR        : '\u2299'; // (8857)	⊙	CIRCLED DOT OPERATOR	eingekreister Punktoperator
CIRCLED_ASTERISK_OPERATOR   : '\u229B'; // (8859)	⊛	CIRCLED ASTERISK OPERATOR	eingekreister Sternoperator
SQUARED_TIMES               :' \u22A0'; // (8864)	⊠	SQUARED TIMES	eingerahmtes Multiplikationszeichen
SQUARED_DOT_OPERATOR        : '\u22A1'; // (8865)	⊡	SQUARED DOT OPERATOR	eingerahmter Punktoperator

MINUS           : '-' OP_SFX?;
CIRCLED_DASH    : '\u229D'; // (8861)	⊝	CIRCLED DASH	eingekreister Gedankenstrich
SQUARED_MINUS   : '\u229F'; // (8863)	⊟	SQUARED MINUS	eingerahmtes Minuszeichen
CIRCLED_MINUS   : '\u2296'; // (8854)	⊖	CIRCLED MINUS	eingekreistes Minuszeichen

PLUS            : '+' OP_SFX?;
CIRCLED_PLUS    : '\u2295'; // (8853)	⊕	CIRCLED PLUS	eingekreistes Pluszeichen
SQUARED_PLUS    : '\u229E'; // (8862)	⊞	SQUARED PLUS	eingerahmtes Pluszeichen

LGUILLEMETS: '<' '<' | '«' | '‹';
RGUILLEMETS: '>''>' | '»' | '›';
GREATEREQUAL: '>' '=' | '\u2265';
EQV         : '<->' | '\u2194';
LESSEQUAL   : '<' '=' | '\u2264';


LESS                            : '<' OP_SFX?;
LESS_THAN_WITH_DOT              : '\u22D6'; // (8918)	⋖	LESS-THAN WITH DOT	kleiner als mit Punkt
VERY_MUCH_LESS_THAN             : '\u22D8'; // (8920)	⋘	VERY MUCH LESS-THAN	Sehr viel kleiner als
LESS_THAN_EQUAL_TO_OR_GREATER_THAN: '\u22DA'; // (8922)	⋚	LESS-THAN EQUAL TO OR GREATER-THAN	kleiner als, gleich oder größer als
EQUAL_TO_OR_LESS_THAN           : '\u22DC'; // (8924)	⋜	EQUAL TO OR LESS-THAN	gleich oder kleiner als
EQUAL_TO_OR_PRECEDES            : '\u22DE'; // (8926)	⋞	EQUAL TO OR PRECEDES	gleich oder vorangehend
DOES_NOT_PRECEDE_OR_EQUAL       : '\u22E0'; // (8928)	⋠	DOES NOT PRECEDE OR EQUAL	weder vorangehend oder gleich
NOT_SQUARE_IMAGE_OF_OR_EQUAL_TO : '\u22E2'; // (8930)	⋢	NOT SQUARE IMAGE OF OR EQUAL TO	kein viereckiges Bild oder gleich
SQUARE_IMAGE_OF_OR_NOT_EQUAL_TO : '\u22E4'; // (8932)	⋤	SQUARE IMAGE OF OR NOT EQUAL TO	viereckiges Bild oder ungleich
PRECEDES                        : '\u227A'; // (8826)	≺	PRECEDES	vorangehend
PRECEDES_OR_EQUAL_TO            : '\u227C'; // (8828)	≼	PRECEDES OR EQUAL TO	vorangehend oder gleich
PRECEDES_OR_EQUIVALENT_TO       : '\u227E'; // (8830)	≾	PRECEDES OR EQUIVALENT TO	vorangehend oder äquivalent
NOT_A_SUBSET_OF                 : '\u2284'; // (8836)	⊄	NOT A SUBSET OF	ist keine ;// (echte) Teilmenge von
SUBSET_OF_OR_EQUAL_TO           : '\u2286' | '\\subseteq'; // (8838)	⊆	SUBSET OF OR EQUAL TO	Teilmenge oder gleich


GREATER                               : '>' OP_SFX?;
SQUARE_ORIGINAL                       : '\u2290'; // (8848)	⊐	SQUARE ORIGINAL OF	viereckiges Original
SQUARE_ORIGINAL_OF_OR_EQUAL_TO        : '\u2292'; // (8850)	⊒	SQUARE ORIGINAL OF OR EQUAL TO	viereckiges Original oder gleich
GREATER_THAN_WITH_DOT                 : '\u22D7' | '\\gedot'; // (8919)	⋗	GREATER-THAN WITH DOT	größer als mit Punkt
VERY_MUCH_GREATER_THAN                : '\u22D9' | '\\gg'   ; // (8921)	⋙	VERY MUCH GREATER-THAN	sehr viel größer als
GREATER_THAN_EQUAL_TO_OR_LESS_THAN    : '\u22DB'; // (8923)	⋛	GREATER-THAN EQUAL TO OR LESS-THAN	größer als, gleich oder kleiner als
EQUAL_TO_OR_GREATER_THAN              : '\u22DD'; // (8925)	⋝	EQUAL TO OR GREATER-THAN	gleich oder größer als
EQUAL_TO_OR_SUCCEEDS                  : '\u22DF'; // (8927)	⋟	EQUAL TO OR SUCCEEDS	gleich oder nachfolgend
DOES_NOT_SUCCEED_OR_EQUAL             : '\u22E1'; // (8929)	⋡	DOES NOT SUCCEED OR EQUAL	weder nachfolgend oder gleich
NOT_SQUARE_ORIGINAL_OF_OR_EQUAL_TO    : '\u22E3'; // (8931)	⋣	NOT SQUARE ORIGINAL OF OR EQUAL TO	kein viereckiges Original oder gleich
SQUARE_ORIGINAL_OF_OR_NOT_EQUAL_TO    : '\u22E5'; // (8933)	⋥	SQUARE ORIGINAL OF OR NOT EQUAL TO	viereckiges Original oder ungleich
SUCCEEDS                              : '\u227B'; // (8827)	≻	SUCCEEDS	nachfolgend
SUCCEEDS_OR_EQUAL_TO                  : '\u227D'; // (8829)	≽	SUCCEEDS OR EQUAL TO	nachfolgend oder gleich
SUCCEEDS_OR_EQUIVALENT_TO             : '\u227F'; // (8831)	≿	SUCCEEDS OR EQUIVALENT TO	nachfolgend oder äquivalent
DOES_NOT_PRECEDE                      : '\u2280'; // (8832)	⊀	DOES NOT PRECEDE	nicht vorangehend
DOES_NOT_SUCCEED                      : '\u2281'; // (8833)	⊁	DOES NOT SUCCEED	nicht nachfolgend
SUPERSET_OF                           : '\u2283'; // (8835)	⊃	SUPERSET OF	ist ;// (echte) Obermenge von
NOT_A_SUPERSET_OF                     : '\u2285'; // (8837)	⊅	NOT A SUPERSET OF	ist keine ;// (echte) Obermenge von
SUPERSET_OF_OR_EQUAL_TO               : '\u2287'; // (8839)	⊇	SUPERSET OF OR EQUAL TO	Obermenge oder gleich
SQUARE_IMAGE_OF                       : '\u228F'; // (8847)	⊏	SQUARE IMAGE OF	viereckiges Bild
SQUARE_IMAGE_OF_OR_EQUAL_TO           : '\u2291'; // (8849)	⊑	SQUARE IMAGE OF OR EQUAL TO	viereckiges Bild oder gleich


IMPLICIT_IDENT: '<' (LETTER)+ '>' ('$lmtd')? -> type(IDENT);
PRIMES      :	('\'')+;
CHAR_LITERAL: '\''
    ((' '..'&') |
     ('('..'[') |
     (']'..'~') |
     ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"' | 'u' HEX ))
    )
    '\''
;

WS:  [ \t\n\r\u00a0]+ -> channel(HIDDEN); //'\u00A0 = non breakable whitespace
STRING_LITERAL:'"' ('\\' . | ~( '"' | '\\') )* '"' ;

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
    RATIONAL_LITERAL ('r' | 'R')?
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