--# -path=.:../resourceAbstract:../prelude:../resourceGerman:../resource

resource myResourceExtGer = open ResourceGer, Prelude, PredicationGer, ParadigmsGer, MorphoGer, SyntaxGer, ResourceExtGer, formatOCL in {

-- FIXME: some uses of vSehen below might well be wrong, check this!
-- (the errors might be for strong verbs without umlaut in present tense,
-- the operation verbStrongSingen/vSingen was missing)

------------------------------------------------------------------------------------------
-- possible extensions of the resource grammars
------------------------------------------------------------------------------------------

oper 
	-- There should probably be a special category for punctuation marks.
	-- For the moment, we will just use strings.
    colon : Str = ":";
    comma : Str = ",";

    PostPunctuate : S -> Str -> S = \text, p ->
        {s = table {order => text.s ! order ++ p}; lock_S = <>};
        
    PrePunctuate : Str -> S -> S = \p, text ->
        {s = table {order => p ++ text.s ! order}; lock_S = <>};
        
    Parentheses : S -> S = \text -> 
        {s = table {order => "(" ++ text.s ! order ++ ")"}; lock_S =<>} ;
    
    parenthCN : CN -> S -> CN = \cn, text ->
	nameCN cn ((Parentheses text).s!Main);
        
    keinDet  = mkDeterminerSg (table {
          Masc => (caselist "kein" "keinen" "keinem" "keines");
	  Fem => caselist "keine" "keine" "keiner" "keiner";
	  Neut => caselist "kein" "kein" "keinem" "keines"
    }) Strong;

    keineDet = mkDeterminerPl (caselist "keine" "keine" "keinen" "keinen") Strong;

    irgendeinDet  = mkDeterminerSg (table {
          Masc => (caselist "irgendein" "irgendeinen" "irgendeinem" "irgendeines");
	  Fem => caselist "irgendeine" "irgendeine" "irgendeiner" "irgendeiner";
	  Neut => caselist "irgendein" "irgendein" "irgendeinem" "irgendeines"
    }) Strong ** {lock_Det = <>} ;

    irgendwelcheDet = mkDeterminerPl (caselist "irgendwelche" "irgendwelche" "irgendwelchen" "irgendwelchen") Weak;

    dasselbe : Number => Gender => Case => Str = table {
  	   Sg => table {
	   	  Masc  => caselist "derselbe" "denselben" "demselben"  "desselben";
		  Fem   => caselist "dieselbe" "dieselbe"  "derselben"  "derselben";
		  Neut  => caselist "dasselbe" "dasselbe"  "demselben"  "desselben"
	   };	  	     
	   Pl => \\_ => caselist "dieselben" "dieselben" "denselben" "derselben"
  } ;

  dasselbeObjWie : CN -> NP -> NP = \class, insta ->
  	    { s = table { 
	      	    NPCase c => dasselbe ! insta.n ! class.g ! c ++ class.s ! Weak ! insta.n ! c ++ "wie" ++ insta.s ! NPCase Nom ;
		    _  => nonExist
		  };
	      n = insta.n;
	      p = insta.p;
	      pro = False;
	      lock_NP = <>
 	    } ;


--    ItNP : NP = pronNounPhrase pronEs;
--    pronEs = mkPronPers "es" "es" "ihm" "seines" "sein" Sg P3;
-- Vocabulary	
--    echtAdj1		: Adj1	 = ParadigmsGer.adjGen "echt";
    absValueN		: N    	 = nGen "Absolutbetrag" "Absolutbetrages" "Absolutbetraege" masculine;
    alwaysAdV		: AdV	 = mkAdV "immer";
    amountN		: N	 = nFrau "Anzahl";
    appendV		: V	 = vPartWeak "haengen" "an";
    arrayN		: N	 = nFrau "Reihung";
    associateTV		: TV	 = mkTV (vSehen "verbinden" "verbindet" "verband" "verbuende" "verbunden" ) "mit" dative;
    associatedWithAdj2	: Adj2	 = aPastPartTV associateTV;
    attributeN 		: N    	 = nGen "Attribut" "Attributs" "Attribute" neuter;
    bagN		: N    	 = nFrau "Multimenge";
    beginN		: N	 = nGen "Beginn" "Beginns" "Anfaenge" masculine;
    booleanAP		: AP	 = AdjP1 (ParadigmsGer.adjGen "boolsch");
    calculatedByAdj2	: Adj2	 = aPastPartTV (mkTV (vGratulieren "berechnen") "durch" accusative);
    capitalN		: N	 = mkN "Grossbuchstabe" "Grossbuchstaben" "Grossbuchstaben" "Grossbuchstaben" "Grossbuchstaben" "Grossbuchstaben" masculine;
    caseN		: N	 = nRaum "Fall" "Faelle";
    classN		: N	 = nFrau "Klasse";
    collectionN		: N	 = nFrau "Sammlung";
    concatenationN	: N	 = nFrau "Aneinanderkettung";
    conditionN 		: N 	 = nFrau "Bedingung";
    constantN 		: N 	 = nFrau "Konstante";
    constructorN	: N	 = nVater "Konstruktor" "Konstruktoren";
    containTV 		: TV	 = mkTV (vSehen "enthalten" "enthaelt" "enthielt" "enthielte" "enthalten") [] accusative;
    convertV		: V	 = vPartWeak "wandeln" "um";
    createV		: V	 = vSehen "erschaffen" "erschafft" "erschuf" "erschuefe" "erschaffen";
    differentAP		: AP	 = AdjP1 (ParadigmsGer.adjGen "verschieden");
    directAP		: AP	 = AdjP1 (mkAdj1 "direkt" "direkt");
    elementN    	: N    	 = nGen "Element" "Elements" "Elemente" neuter;
    emergeV		: V	 = vSehen "entstehen" "entsteht" "entstand" "entstuende" "entstanden";
    emptyAP		: AP	 = AdjP1 (mkAdj1 "leer" "leer");
    endN		: N	 = nGen "Ende" "Endes" "Enden" neuter;
    equalAdj2		: Adj2	 = mkAdj2 (ParadigmsGer.adjInvar "gleich") [] dative;
    evaluationN		: N    	 = nFrau "Auswertung";
    exceptionN		: N	 = nFrau "Ausnahme";
    expressionN		: N	 = nRaum "Ausdruck" "Ausduercke";
    firstAP		: AP   	 = AdjP1 (mkAdj1 nonExist "erst");
    floorV		: V	 = vPartWeak "runden" "ab"; -- CHECK! %%-- vPart "runden" "rundet" "runde" "gerundet" "ab";
    followAP 		: AP 	 = AdjP1 (ParadigmsGer.adjGen "folgend");
    givenTV		: TV	 = tvDir (mkV "geben" "gibt" "gib" "gab" "gaebe" "gegeben");
    greatAdjDeg 	: AdjDeg = aDeg3 "gross" "groesser" "groessten";
    gteAdj2		: Adj2 	 = mkAdj2 (ParadigmsGer.adjInvar "mindestens") "" nominative; --%%
    holdTV		: TV	 = mkTV holdV "fr" accusative;
    holdV 		: V 	 = vSehen "gelten" "gilt" "galt" "gaelte" "gegolten";
    implyV		: V	 = vWeak "implizieren";
    indexN		: N    	 = mkN "Index" "Index" "Index" "Index" "Indices" "Indices" masculine;
    initializeTV	: TV	 = mkTV (vGratulieren "initialisieren") [] accusative;
    instanceN		: N    	 = nFrau "Instanz";
    integerAP		: AP 	 = AdjP1 (ParadigmsGer.adjGen "ganz");
    integerN		: N 	 = nFrau "Ganzzahl";
    intersectionN       : N    	 = nTisch "Schnitt";  
    invariantN 		: N 	 = nFrau "Invariante";
    lastAP		: AP   	 = AdjP1 (mkAdj1 nonExist "letzt");
    lengthN		: N	 = nFrau "Laenge";
    littleAdjDeg	: AdjDeg = aReg "klein" ;
    ltAdj2		: Adj2   = mkAdj2 (ParadigmsGer.adjGen "kleiner") "als" nominative;
    lteAdj2		: Adj2 	 = mkAdj2 (ParadigmsGer.adjInvar "maximal") "" nominative; -- %%
    maximumN		: N    	 = mkN "Maximum" "Maximum" "Maximum" "Maximums" "Maxima" "Maxima" neuter;
    minimumN		: N    	 = mkN "Minimum" "Minimum" "Minimum" "Minimums" "Minima" "Minima" neuter;
    minisculeN		: N	 = mkN "Kleinbuchstabe" "Kleinbuchstaben" "Kleinbuchstaben" "Kleinbuchstaben" "Kleinbuchstaben" "Kleinbuchstaben" masculine;
    nameN		: N    	 = (mkN "Name" "Namen" "Namen" "Namens" "Namen" "Namen" masculine);
    naturallyAdA	: AdA	 = ParadigmsGer.mkAdA "echt";
    negativeN		: N    	 = nGen "Negative" "Negativen" "Negativen" neuter;
    normallyAdV		: AdV	 = mkAdV "normal";
    nullN		: N	 = nTisch "Null-Wert"; -- FIXME? %%
    numberN		: N    	 = nFrau "Zahl";
    objectN		: N	 = nGen "Objekt" "Objekts" "Objekte" neuter;
    occurrenceN		: N	 = nGen "Vorkommnis" "Vorkommnisses" "Vorkommnisse" neuter;
    oclTypeN		: N    	 = nSoldat "OCL-Typ";
    operationN 		: N    	 = nFrau "Operation";
    postconditionN 	: N 	 = nFrau "Nachbedingung";
    preconditionN 	: N	 = nFrau "Vorbedingung";
    predicationN	: N	 = nFrau "Aussage";
    previousAP		: AP	 = apReg "vorherig"; 
    productN		: N	 = nBein "Produkt";
    propertyAP		: AP	 = apReg "vereigenschaftet"; -- %%%
    propertyN		: N	 = nFrau "Eigenschaft";
    queryN		: N	 = nFrau "Anfrage";
    realAP		: AP	 = AdjP1 (ParadigmsGer.adjGen "reell");
    regardV		: V	 = vGratulieren "betrachten"; 
    regardedAsAdj2	: Adj2	 = (mkAdj2 (aPastPart regardV) "als" nominative);
    resultN		: N    	 = nGen "Ergebnis" "Ergebnisses" "Ergebnisse" neuter;
    resultTV		: TV	 = mkTV ((vSehen "ergeben" "ergibt" "ergab" "ergaebe" "ergeben")) [] accusative;
    roundV		: V	 = vWeak "runden"; 
    sequenceN		: N    	 = nFrau "Folge";
    setN 		: N    	 = nFrau "Menge";
    shouldVV		: VV	 = vsAux (mkV "sollten" "sollte" "sollt" "sollte" "soellte" "gesollt"); --%%
    sizeN		: N	 = nFrau "Maechtigkeit";
    sortV		: V	 = vGratulieren "sortieren"; -- CHECK! %
    specifiedInAdj2	: Adj2	 = mkAdj2 (ParadigmsGer.adjGen "festgelegt") "in" dative; --%%
    startN		: N	 = nRaum "Anfang" "Anfaenge";
    stateN		: N    	 = nRaum "Zustand" "Zustaende";
    stringN		: N	 = nFrau "Zeichenkette";
    subpartN		: N	 = nRaum "Ausschnitt" "Auschnitte";
    subsequenceN	: N	 = nFrau "Teilfolge";
    subtypeN		: N	 = nSoldat "(Unter-)Typ";
    sumN		: N	 = nFrau "Summe";
    supertypeN		: N    	 = nSoldat "(Ober-)Typ";
    terminateV		: V	 = vWeak "terminieren";
    thenAdV		: AdV	 = mkAdV "dann";
    throwV		: V	 = vPartWeak "loesen" "aus";
    trueAP		: AP	 = apReg "wahr";
    trueN		: N	 = nMesser "Wahr"; -- %%%%
    truthvalueN		: N	 = nGen "Wahrheitsgehalt" "Wahrheitsgehaltes" "Wahrheitsgehaelter"  masculine;
    typeAdj2		: Adj2	 = mkAdj2 (ParadigmsGer.adjInvar "vom") "Typ" nominative; -- %%%%
    typeN		: N    	 = nSoldat "Typ";
    unionN	        : N    	 = nFrau "Vereinigung";
    uniqueAP		: AP	 = AdjP1 (ParadigmsGer.adjGen "eindeutig");
    updateTV		: TV	 = mkTV (vGratulieren "aktualisieren") [] accusative;
    valueN		: N	 = nTisch "Wert";

    fullfilledAdj1	: Adj1	 = ParadigmsGer.adjGen "erfuellt"; --%% not generated from a verb

    iffSubj		: Subj   = {s = ["genau dann wenn"]; lock_Subj = <>}; -- %%
    givenSubj   	: Subj   = {s = "gegeben"; lock_Subj = <>};
    thenSubj   		: Subj   = {s = "dann"; lock_Subj = <>};

--These are additions/replacements for opers from the resource grammars
    funGen : N -> Fun = \n ->
	funGenCN (UseN n);
    funGenCN : CN -> Fun = \n ->
  	mkFunCN n (ParadigmsGer.mkPrep "" Gen);
    mkFunCN : CN -> Prep -> Fun = \cn,prep ->
    cn ** {s2 = prep.s ; c = prep.c; lock_Fun = <>} ;
    mkFun : N -> Prep -> Fun = \n, prep ->
  	mkFunCN (UseN n) prep;
    funVonCN : CN -> Fun = \n ->
  	mkFunCN n (ParadigmsGer.mkPrep "von" Dat);
    funVon : N -> Fun = \n ->
  	funVonCN (UseN n);

    nameCN 		: CN -> Str -> CN = \cn, str -> AdvCN cn (mkAdV str);
    predNegA2 		: Adj2 -> NP -> NP -> S = \F, x, y -> PredVP x (NegVG (PredAP (ComplAdj F y)));
    withoutConj			 = ss "ohne" ** {n = Sg; lock_Conj = <>} ; --has type 'Conj'

    Loc2NP 		: NP -> AdV = PrepNP (ParadigmsGer.mkPrep "an" Dat);
    forNP		: NP -> AdV = PrepNP (ParadigmsGer.mkPrep "fuer" Acc);

    mkFun2 		: CN -> Preposition -> Case -> Preposition -> Case -> Fun2 = \cn, p1, case1, p2, case2 ->
			{ 
				s = cn.s; 
				g = cn.g; 
				s2 = p1; 
				c = case1; 
				s3 = p2; 
				c2 = case2; 
				lock_Fun2 = <>
			};
    mkFun2VonBis 	: CN -> Fun2 = \cn ->
			mkFun2 cn "von" dative "bis" dative;
    adv2ada 		: AdV -> AdA = \a -> mkAdA a.s;
    v2vs 		: V -> VS = \v -> -- %% mkVS does the same
			{
				s = v.s;
				s1 = v.s1;
				s2 = v.s2;
				lock_VS = <>
			};
    getNomNP 		: NP -> Str = \np ->
				(np.s!NPCase nominative);

    getNomSgCN 		: CN -> Str = \cn ->
				(cn.s!Strong!Sg!nominative);
  
    aPastPartTV 	: TV -> Adj2 
	= \tv -> mkAdj2 (aPastPart (VTrans tv)) tv.s3 tv.c;

	-- This is probably not very good grammatically.
    np2s 		: NP -> S = \np -> {	
				s = table {
					order => np.s ! NPCase nominative
				} ;
				lock_S = <>
			};
    ap2s 		: AP -> S = \ap -> {
				s = table {
					order => ap.s ! APred
				};
				lock_S = <>
			};
    AdVS 		: AdV -> S -> S = \adv, sent -> {
				s = table { 
					order => adv.s ++ sent.s!order
				};
				lock_S = <>
			};

    ifThenElseNP :  S -> NP -> NP -> NP = \cond, t, e -> 
	{
 	s = \\c => t.s!c ++ [", wenn"] ++ cond.s!Sub ++ ", ansonsten" ++ e.s!c;
 	n = t.n; p = t.p; pro = False; lock_NP = <>
	};



-- subj a then b
    SubjThen     	: Subj -> S -> S -> S = \subj, a, b -> {
		s = table {
			Main => subj.s ++ a.s!Main ++ thenSubj.s ++ b.s!Inv;
			Inv  => thenSubj.s ++ b.s!Inv ++ a.s!Main;
			Sub  => subj.s ++ a.s!Sub ++ thenSubj.s ++ b.s!Sub
		}; 
		lock_S = <>
	};

-- if a then this implies b
    --SubjImplies : S -> S -> S = \a, b ->
        --{s = IfSubj.s ++ a.s ++ thenSubj.s ++ (PredVP ThisNP (PosVG (PredVS (v2vs implyV) b))).s; lock_S =<>};
    SubjImplies	: S-> S -> S = \a, b -> {
	s = table {
--		Main => IfSubj.s ++ a.s!Sub ++ "dann" ++ (PredVP ThisNP (PosVG (PredVS (v2vs implyV) b))).s!Sub;
		Main => IfSubj.s ++ a.s!Sub ++ "dann" ++ (PredVP ThisNP (PosVG (PredVS (v2vs implyV) b))).s!Inv;
		Inv  => (implS a b).s!Inv;
		Sub  => (implS a b).s!Sub
	};
	lock_S = <>
    };

-- if a then this implies b otherwise c
    SubjIfImpliesOtherwise : S -> S -> S -> S = \a, b, c -> {
	s = table {
		Main => (SubjImplies a b).s!Main ++ comma ++ "wenn nicht" ++ comma ++ "dass" ++ c.s!Sub;
		Inv  => "SubjIfImpliesOtherwise";--nonExist;
		Sub  => "SubjIfImpliesOtherwise"--nonExist
	};
	lock_S =<>
    };

-- at least one is build as a determiner

    atLeastOneDet : Det = {
	s = \\g,c => "mindestens" ++ SomeDet.s!g!c;
	n = SomeDet.n;
	a = SomeDet.a;
	lock_Det = <>
    };

-- The next step is at least one of the as a determiner

    atLeastOneOfTheNP : CN -> NP = \cn ->{
	s = \\npc => "mindestens" ++ einErEEs!cn.g!npc ++ "der" ++ cn.s!Weak!Pl!genitive;
	n = Sg;
	p = P3;
	pro = True;
	lock_NP = <>
    };

    oper einErEEs : Gender => NPForm => Str= table {
	feminine => 	table {
				NPCase nominative => "eine";
				NPCase accusative => "eine";
				NPCase dative     => "einer";
				NPCase genitive   => "einErEEs";--nonExist;
				_ 		  => "einErEEs"--nonExist
			};
	masculine => 	table {
				NPCase nominative => "einer";
				NPCase accusative => "einen";
				NPCase dative     => "einem";
				NPCase genitive   => "einErEEs";--nonExist;
				_ 		  => "einErEEs"--nonExist
			};
	neuter => 	table {
				NPCase nominative => "eines";
				NPCase accusative => "einem";
				NPCase dative     => "eines";
				NPCase genitive   => "einErEEs";--nonExist;
				_ 		  => "einErEEs"--nonExist
			}
    };





-- This differs from univS, in that the "for all" part comes first.
    forAllS : CN -> S -> S = \A,B -> {
	s = \\o => (AdVS ((prepPhrase ((mkPrep "fuer" accusative) ** {lock_Prep = <>}) (DetNP AllDet A)) ** {lock_AdV = <>}) B).s!o;
	lock_S = <>
    };

-- This is a cheat, but it sounds better than forAllS and univS
    forAllHoldS  : CN -> S -> S = \A,B -> {
	s = table {
		Main => (prepPhrase ((mkPrep "fuer" accusative) ** {lock_Prep = <>}) (DetNP AllDet A)).s ++ "gilt:" ++ B.s!Main;
		Sub  => (prepPhrase ((mkPrep "fuer" accusative) ** {lock_Prep = <>}) (DetNP AllDet A)).s ++ "gilt:" ++ B.s!Main;
		Inv  => (prepPhrase ((mkPrep "fuer" accusative) ** {lock_Prep = <>}) (DetNP AllDet A)).s ++ "gilt:" ++ B.s!Main
		-- This is strange, in a subject-less sentence-introduction the word order is always the same
	};
	lock_S = <>
    };


--This is from Logical.gf
    negS : S -> S = \A ->
      PredVP ItNP (NegVG (PredNP (DefOneNP (CNthatS (UseN (nRaum "Fall" "Faelle")) A)))) ;
    univS : CN -> S -> S = \A,B ->
      PredVP ItNP (AdvVP (PosVG (PredVS (mkVS holdV) B))
                    (mkPP Acc "fuer" (DetNP (AllDet) A))) ;
    existS : CN -> S -> S= \A,B ->
      PredVP ItNP (PosTV (tvDir (vSehen "geben" "gibt" "gab" "gaebe" "gegeben"))
                     (IndefOneNP (ModRC A (RelSuch B)))) ;
    existManyS : CN -> S -> S = \A,B ->
     PredVP ItNP (PosTV (tvDir (vSehen "geben" "gibt" "gab" "gaebe" "gegeben"))
                    (IndefManyNP (ModRC A (RelSuch B)))) ;

    -- For the bulleted lists only Main word order sentences are needed:
    onlyMainS : Str -> S = \str -> {
	s = table {
		Main => str;
		_    => "onlyMainS"--nonExist
	};
	lock_S = <>
    };

    --To have some ungrammatical thing ( bullets or even a figure), that is referred to in the sentence.
    --This is a dumb function which just glues the thing at the end of the sentence.
    glueStrToS : S -> Str -> S = \sentence, str -> {
	s = \\order => sentence.s!order ++ str;
	lock_S = <>
    };

-- if A then B
    ifThenS     : S -> S -> S = \a, b -> {
		s = table {
			Main => "wenn" ++ a.s!Sub ++ comma ++ thenSubj.s ++ b.s!Inv;
			Inv  => b.s!Inv ++ comma ++ "wenn" ++ a.s!Sub;
			Sub  => "wenn" ++ a.s!Sub ++ comma ++ b.s!Sub
		}; 
		lock_S = <>
	};

-- to convert a table Order => Str to a S
    s2S : (Order => Str) -> S = \ps -> {
	s = ps;
	lock_S = <>
    };	

-- bold or
	boldOrConj = {
		s = mkBold "oder";
		n = Sg;
		lock_Conj = <>
	};

};
