--# -path=.:../prelude:../resourceAbstract:../resourceEnglish

resource myResourceExtEng = open Prelude, ResourceEng, ResourceExtEng, ParadigmsEng, MorphoEng, ExtraEng, SyntaxEng, TypesEng, formatOCL in {
------------------------------------------------------------------------------------------
-- possible extensions of the resource grammars
------------------------------------------------------------------------------------------


oper 
    keinDet = mkDet Sg "no";

    keineDet = mkDet Pl "no";

    irgendeinDet = mkDet Sg "any";

    irgendwelcheDet = mkDet Pl  "any";

    dasselbeObjWie : CN -> NP -> NP = \class, inste ->
  	    { s = table { 
	      	    casel => "the" ++ "same" ++ class.s!inste.n!(toCase casel) ++ "as" ++ inste.s!NomP
		  };
	      n = inste.n;
	      p = inste.p;
		lock_NP = <>
 	    } ;


-- Vocabulary	    
--    echtAdj1		: Adj1	 = mkAdj1 "natural";        
    absValueN		: N    	 = nNonhuman "absolute value";
    alwaysAdV		: AdV	 = mkAdvPre "always";
    amountN		: N	 = nNonhuman "amount";
    appendV		: V	 = vReg "append";
    arrayN		: N	 = nNonhuman "array";    
    associateTV		: TV	 = mkTV (vReg "associate") "with";
    associatedWithAdj2	: Adj2	 = mkAdj2 "associated" "with";
    attributeN 		: N    	 = nNonhuman "attribute";
    bagN		: N    	 = nNonhuman "bag";
    beginN		: N	 = nNonhuman "beginning";
    booleanAP		: AP	 = apReg "boolean";
    calculatedByAdj2	: Adj2	 = mkAdj2 "calculated" "by";
    capitalN		: N	 = nNonhuman "uppercase letter";
    caseN		: N	 = nNonhuman "case";
    classN		: N	 = nNonhuman "class";
    collectionN		: N	 = nNonhuman "collection";
    concatenationN	: N	 = nNonhuman "concatenation";
    conditionN 		: N	 = nNonhuman "condition";
    constantN 		: N    	 = nNonhuman "constant";
    constructorN 	: N    	 = nNonhuman "constructor";
    containTV 		: TV	 = tvGenDir "contain";
    convertV		: V	 = vReg "convert";
    createV		: V	 = mkV "create" "creates" "created" "created";
    differentAP		: AP	 = apReg "different";
    directAP		: AP	 = apReg "direct";
    elementN    	: N    	 = nNonhuman "element";
    emergeV		: V	 = vReg "emerge";
    emptyAP		: AP	 = apReg "empty";
    endN		: N	 = nNonhuman "end"; 
    equalAdj2		: Adj2	 = mkAdj2 "equal" "to";
    evaluationN		: N    	 = nNonhuman "evaluation";
    exceptionN 		: N 	 = nNonhuman "exception";
    expressionN		: N	 = nNonhuman "expression";
    firstAP		: AP   	 = apReg "first";
    floorV		: V	 = vPartReg "round" "down";
    followAP    	: AP     = apReg "following";
    givenTV		: TV = tvDir (mkV "give" "gives" "gave" "given");
    greatAdjDeg 	: AdjDeg = aReg "great";
    gteAdj2		: Adj2 	 = mkAdj2 "at" "least";
    holdTV		: TV	 = mkTV (vReg "hold") "for";
    holdV       	: V 	 = vReg "hold";
    implyV      	: V 	 = mkV "imply" "implies" "implied" "implied";
    indexN		: N    	 = mkN "index" "index'" "indices" "indices'" nonhuman;
    initializeTV	: TV	 = tvGenDir "initialize";
    instanceN		: N    	 = nNonhuman "instance";
    integerAP		: AP 	 = apReg "integer";
    integerN 		: N 	 = nNonhuman "integer";
    intersectionN       : N    	 = nNonhuman "intersection";
    invariantN 		: N 	 = nNonhuman "invariant";
    lastAP		: AP   	 = apReg "last";    
    lengthN		: N	 = nNonhuman "length";
    littleAdjDeg	: AdjDeg = aReg "small";
    ltAdj2		: Adj2 	 = mkAdj2 "less" "than";
    lteAdj2		: Adj2 	 = mkAdj2 "at" "most";
    maximumN		: N    	 = mkN "maximum" "maximums" "maxima" "maxima's" nonhuman;
    minimumN		: N    	 = mkN "minimum" "minimums" "minima" "minima's" nonhuman;
    minisculeN		: N	 = nNonhuman "lowercase letter";
    nameN		: N    	 = nNonhuman "name";
    naturallyAdA	: AdA	 = mkAdA "naturally";    
    negativeN		: N    	 = nNonhuman "negative";
    normallyAdV		: AdV	 = mkAdv "normally";
    nullN 		: N 	 = nNonhuman "null value";
    numberN		: N    	 = nNonhuman "number";
    objectN		: N	 = nNonhuman "object";
    occurrenceN		: N	 = nNonhuman "occurrence";
    oclTypeN		: N    	 = nNonhuman "OCL type";
    operationN 		: N    	 = nNonhuman "operation";
    postconditionN 	: N	 = nNonhuman "post-condition";
    preconditionN 	: N	 = nNonhuman "pre-condition";
    predicationN	: N	 = nNonhuman "predication";
    previousAP		: AP   	 = apReg "previous";
    productN		: N	 = nNonhuman "product";
    propertyAP		: AP   	 = apReg "property";
    propertyN		: N	 = nNonhuman "property";
    queryN		: N	 = nNonhuman "query";
    realAP		: AP	 = apReg "real";
    regardV		: V	 = vReg "regard";
    regardedAsAdj2	: Adj2	 = mkAdj2 "regarded" "as";
    resultN		: N    	 = nNonhuman "result";
    resultTV		: TV	 = mkTV (vReg "result") "in";
    roundV		: V	 = vReg "round";
    sequenceN		: N    	 = nNonhuman "sequence";
    setN 		: N    	 = nNonhuman "set";
    shouldVV		: VV 	 = (mkVerbAux "should" "should" "should" "should") ** {lock_VV = <>} ;
    sizeN		: N	 = nNonhuman "size";
    sortV		: V	 = vReg "sort";
    specifiedInAdj2	: Adj2	 = mkAdj2 "specified" "in";
    startN		: N	 = nNonhuman "start";
    stateN		: N    	 = nNonhuman "state";
    stringN		: N	 = nNonhuman "String";
    subpartN		: N	 = nNonhuman "subpart";
    subsequenceN	: N	 = nNonhuman "subsequence";
    subtypeN		: N    	 = nNonhuman "subtype";
    sumN		: N	 = nNonhuman "sum";
    supertypeN		: N    	 = nNonhuman "supertype";
    terminateV		: V	 = vReg "terminate";
    thenAdV		: AdV	 = mkAdvPre "than";
    throwV 		: V 	 = mkV "throw" "throws" "throwed" "thrown";
    trueAP    : AP     = apReg "true";
    trueN		: N	 = nNonhuman "true";
    truthvalueN		: N	 = nNonhuman "truth value";
    typeAdj2    : Adj2 = mkAdj2 "of" "type";
    typeN		: N    	 = nNonhuman "type"; 
    unionN	        : N    	 = nNonhuman "union";
    uniqueAP		: AP	 = apReg "unique";
    updateTV		: TV	 = tvGenDir "update";
    valueN		: N	 = nNonhuman "value";

    iffSubj		: Subj   = {s = "if and only if"; lock_Subj = <>};
    givenSubj 		: Subj   = {s = "given"; lock_Subj = <>};
    thenSubj 		: Subj   = {s = "then"; lock_Subj = <>};

    funGen : N -> Fun = \n -> ParadigmsEng.funOfCN (UseN n);
    funGenCN : CN -> Fun = \cn -> ParadigmsEng.funOfCN cn;
    nameCN : CN -> Str -> CN = \cn, str -> AdvCN cn (mkAdv str);
    predNegA2 : Adj2 -> NP -> NP -> S = \F, x, y -> PredVP x (NegA (ComplAdj F y)) ; 
    withoutConj   = ss "without" ** {n = Sg; lock_Conj = <>} ; --has type 'Conj'

    Loc2NP : NP -> AdV = mkPP "at";
    forNP : NP -> AdV = mkPP "for";

    ifThenElseNP :  S -> NP -> NP -> NP = \cond, t, e -> 
	{
 	s = \\c => t.s!c ++ [", if"] ++ cond.s ++ [", otherwise"] ++ e.s!c;
 	n = t.n; p = t.p; pro = False; lock_NP = <>
	};
	
   
    mkFun2 : CN -> Preposition -> Preposition -> Fun2 = \cn, p1, p2 ->
	{
	s = cn.s; 
	g = cn.g; 
	s2 = p1; 
	s3 = p2;
	lock_Fun2 = <>
	};
    mkFun2VonBis : CN -> Fun2 = \cn ->
	mkFun2 cn "from" "to";

    adv2ada : AdV -> AdA = \a -> 
	{
	s = a.s;
	lock_AdA = <>
	};
	
    v2vs : V -> VS = \v ->
	{
	s = v.s;
	s1 = v.s1;
	lock_VS = <>
	};

    getNomNP : NP -> Str = \np ->
	(np.s!NomP);

    getNomSgCN : CN -> Str = \cn ->
	(cn.s!Sg!Nom);

    aPastPart : V -> Adj1 = \v ->
	mkAdj1 (v.s!PPart);

    mkDet : Number -> Str -> Det = \n,s ->
	mkDeterminer n s ** {lock_Det = <>};

	-- There should probably be a special category for punctuation marks.
	-- For the moment, we will just use strings.
    colon : Str = ":";
    comma : Str = ",";

    PostPunctuate : S -> Str -> S = \text, p ->
        {s = text.s ++ p; lock_S = <>};
        
    PrePunctuate : Str -> S -> S = \p, text ->
        {s = p ++ text.s; lock_S = <>};
        
    Parentheses : S -> S = \text -> 
        {s = "(" ++ text.s ++ ")"; lock_S =<>} ;
    
    parenthCN : CN -> S -> CN = \cn, text ->
        nameCN cn (Parentheses text).s;
        
	-- This is probably not very good grammatically.
    np2s : NP -> S = \np -> {s = np.s ! NomP; lock_S = <>};

	
	-- subj a then b
    SubjThen     : Subj -> S -> S -> S = \subj, a, b ->
        {s = subj.s ++ a.s ++ thenSubj.s ++ b.s; lock_S = <>};

    -- if a then this implies b
    SubjImplies : S -> S -> S = \a, b ->
        {s = IfSubj.s ++ a.s ++ thenSubj.s ++ (PredVP ThisNP (PosVG (PredVS (v2vs implyV) b))).s; lock_S =<>};

    -- if a then this implies b otherwise c
    SubjIfImpliesOtherwise : S -> S -> S -> S = \a, b, c ->
        {s = (SubjImplies a b).s ++ OtherwiseAdv.s ++ c.s; lock_S =<>};
    
    oneNum : Num = {s = table {Nom => "one"; Gen => "one"}; lock_Num = <>};
    
    UseNum : Num -> NP = \num -> UsePN (pnReg (num.s!Nom));

    -- E.g. "at least one"    
    adjNum : Adj2 -> Num -> AP = \adj, num ->
        ComplAdj adj (UseNum num);
    
    -- Modify a CN with an Adj, but leave the CN implicit.
    -- E.g. if we want the text "at least one of the following conditions"
    -- we can construct "at least one condition" using ModAdj,
    -- we can construct "at least one" using ModAdjImpl
    ModAdjImpl : AP -> CN -> CN = \ap, cn -> 
    {s = \\n => if_then_else (Case => Str) ap.p 
           (\\c => ap.s ! AAdj)
           (table {Nom => ap.s ! AAdj ; Gen => variants {}}) ;
     g = cn.g;
     lock_CN = <>
    } ;
    
    -- This differs from univS, in that the "for all" part comes first.
    forAllS : CN -> S -> S = \A,B ->
      {s = (AdVS ((prepPhrase "for" (DetNP AllDet A)) ** {lock_AdV = <>}) B).s;
       lock_S = <>};
       
    AdVS : AdV -> S -> S = \adv, sent ->
    {s = adv.s ++ sent.s; lock_S = <>};

    ap2s : AP -> S = \ap -> {s = ap.s ! AAdj; lock_S = <>};

-- bold or
	boldOrConj = {
		s = mkBold "or";
		n = Sg;
		lock_Conj = <>
	};

};
