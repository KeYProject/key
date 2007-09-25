--# -path=.:../abstract:../resourceAbstract:../prelude:../resourceGerman:../resource

concrete oclLibraryGer of oclLibrary = coreGer ** open Prelude, ResourceGer, internalOperGer, myTypesGer, myResourceExtGer, TypesGer, externalOperGer, ParadigmsGer, PredicationGer, ResourceExtGer, ExtraGer, formatOCL, AtomGer in {



lin


--
-- 'ideomatic expressions', recurring patterns in OCL specs:
--

--    decremented x decr = ...
--    incremented x incr = ...
--    notChanged _ x = ...

--
-- KeY extensions
--
    NullC = mkClass (UseN nullN) "Null";
    nullConforms2 c = {s = ["Null is Untertyp von"] ++ class2id c};
    null = constNoInfl "null";

    excThrown clss a exc = mkPred (inst2np exc) (PredPassV throwV);    

--
-- OclType
--

    OclTypeC = mkClass (UseN oclTypeN) "OclType";
    OclTypeCConforms2OclTypeC = ss ["OclType ist Untertyp von OclType"];
    class2oclType c = constNoInfl (class2id c);
    class2name c = np2inst (IndefOneNP (class2cn c));
    otName t = np2inst (appFun1 (funVon nameN) t);
    otAttributes t = np2inst (appFun1 (funVonCN (AppFun (funGen setN) (DefManyNP (AppFun (funGen nameN) (DefManyNP (UseN  attributeN)))))) (inst2np t));
    otOperations t = np2inst (appFun1 (funVonCN (AppFun (funGen setN) (DefManyNP (AppFun (funGen nameN) (DefManyNP (UseN operationN)))))) (inst2np t));
    otSupertypes t = np2inst (appFun1 (funVonCN (AppFun (funGen setN) (DefManyNP (ModAdj directAP (UseN supertypeN))))) (inst2np t));
    otAllSupertypes t =  np2inst (appFun1 (funVonCN (AppFun (funGen setN) (DetNP AllDet (UseN supertypeN)))) (inst2np t));
    otAllInstancesStrict c t = np2inst (appFun1 (funVonCN (AppFun (funGen setN) (DetNP AllDet ( UseN instanceN)))) (inst2np t));


--
-- OclAny
--
    OclAnyC = mkClass (UseN objectN) "OclAny";
    conforms2OclAny c = { s = (class2id c ++ ["ist Untertyp von OclAny"])};    
    anyOclIsKindOf a t = PredVP (inst2np a) (PosVG (PredCN (AppFun (funVonCN (UseN subtypeN)) (inst2np t))));
    anyOclIsTypeOf a t = ofType a t;
    anyOclAsTypeStrict c a t = a;	     -- This can only ever be used when we have already
                                             -- established the type of a (using anyOclIsTypeOf), 
                                             -- so there is no need to specify the type here again.
--    anyOclAsTypeClass a c = np2inst (advNP (inst2np a) (advAP (AdvAP (adv2ada (mkPP (nominative) "als" (inst2np (IndefOneNP(class2cn c))))) (AdjP1 (aPastPart regardV)))));
    anyOclInState a s = PredVP (DefOneNP (AppFun (funVon stateN) (inst2np a))) (PosVG (PredNP (inst2np s)));
    anyOclIsNew a = (PredVP (inst2np a) (AdvVP (PosVG (PredPassV createV)) (mkPP dative "w�rend" (DefOneNP (UseN operationN)))));

--
-- OclState
--
    OclStateC = mkClass (UseN stateN) "OclState";
    OclStateCConforms2OclStateC = ss ["OclState ist Untertyp von OclState"];




--
-- Integer
--
    IntegerC = mkClass (ModAdj integerAP (UseN numberN)) "Integer";
    int i = np2inst (numNoInfl i.s);
    intAdd = instInfix "plus"; 
    intSub = instInfix "minus";
    intUnaryMinus = instFunVon negativeN;
    intTimes = instInfix "mal";
    intDiv2Real = instInfix ["geteilt durch"];
    intDiv2Int = instInfix ["ganzzahldividiert durch"];
    intMod = instInfix "modulo";
    intAbs = instFunVon absValueN;
    intMax = instFunVon2 maximumN;
    intMin = instFunVon2 minimumN;

    IntegerCConforms2RealC = ss ["Integer ist Untertyp von Real"];
    IntegerCConforms2IntegerC = ss ["Integer"];



--
-- Real
--

lin RealC = mkClass (ModAdj realAP (UseN (nFrau "Zahl"))) "Real";
    RealCConforms2RealC = ss ["Real"];
--    realEq = equalTo;
--    realNeq = notEqualTo;
    realAdd = instInfix "plus"; 
    realSub = instInfix "minus"; 
    realTimes = instInfix "mal"; 
    realDiv = instInfix ["geteilt durch"];
    realUnaryMinus = instFunVon negativeN;
    realAbs = instFunVon absValueN;
    realFloor a = np2inst (advNP (inst2np a) (advAP (AdjP1 (aPastPart floorV))));
    realRound a = np2inst (advNP (inst2np a) (advAP (AdvAP naturallyAdA (AdjP1 (aPastPart roundV)))));
    realMax  = instFunVon2 maximumN;
    realMin = instFunVon2 minimumN;
    realLT = lessThan; 
    realGT = greaterThan;
    realLTE = lteThan;
    realGTE = gteThan; 

    oneSum a b = {s0 = (inst2str a); s1 = (inst2str b); size = LSone};
    consSum t a = {s0 = (a.s0 ++ "," ++ a.s1); s1 = (inst2str t); size = LSmany};	
    sumList2Integer a = 
       case a.size of {
              LSone => instInfix "plus" (constNoInfl a.s0) (constNoInfl a.s1);
              _ => np2inst (appFun1 (funVonCN (UseN sumN)) 
                  (inst2np (instInfix "und" (constNoInfl a.s0) (constNoInfl a.s1))))        
       };
       
    oneProduct a b = {s0 = (inst2str a); s1 = (inst2str b); size = LSone};
    consProduct t a = {s0 = (a.s0 ++ "," ++ a.s1); s1 = (inst2str t); size = LSmany};	
    productList2Integer a = 
       case a.size of {
              LSone => instInfix "mal" (constNoInfl a.s0) (constNoInfl a.s1);
              _ => np2inst (appFun1 (funVonCN (UseN productN)) 
                  (inst2np (instInfix "und" (constNoInfl a.s0) (constNoInfl a.s1))))        
       };

    
--
-- String
--
    StringC = mkClass (UseN stringN) "String";
    StringCConforms2StringC = ss ["String"];
--    stringEq = equalTo;
    stringLiteral lit = constNoInfl lit.s;
    stringSize  = instFunVon lengthN;
    stringConcat  = instFunVon2 concatenationN;
    stringToUpper s = np2inst (advNP (inst2np s) (LocNP (IndefManyNP (UseN capitalN))));
    stringToLower s = np2inst (advNP (inst2np s) (LocNP (IndefManyNP (UseN minisculeN))));
    stringSubstring s a b = np2inst (appFun1 (funVonCN (AppFun (AppFun2 (mkFun2VonBis (UseN subpartN)) (inst2np a)) (inst2np b))) (inst2np s));

--
-- Bool
--
    BooleanC = mkClass (ModAdj booleanAP (UseN valueN)) "Boolean";
    BooleanCConforms2BooleanC = ss ["Boolean"];
    true = trueInst;
    false = falseInst;
--    boolEq = equalTo;
    orBool = instInfix "oder"; 
    xorBool = instInfix ["exklusiv oder"];
    xorBool = instInfix ["exklusiv oder"];
    andBool = instInfix "und";
    notBool = instPrefix "nicht"; 
    impliesBool = instInfix "impliziert";

    bool2sent b = PredVP b (PosVG (PredNP trueInst));
    --sent2bool s = np2inst (DefOneNP (AppFun (funGen truthvalueN) (DefOneNP (CNthatS (UseN predicationN) s))));
    sent2bool s = np2inst (MassNP (nounSubjSentence (UseN trueN) iffSubj s)); --%%%

--
-- Sent 
--
    sentEq a b = SubjS iffSubj a b;
-- use conjunctions
    orS a b = ConjS OrConj (TwoS a b);
    xorS a b = ConjDS EitherOr (TwoS a b);
    andS a b = ConjS AndConj (TwoS a b);
    impliesS a b = SubjImplies a b;
    notS a = negS a;
	-- ifThenElse is a bit tricky: do we really know that t 
	-- and e have the same number and person?
	-- ideally we should have a resource grammar which supports conditional expressions
    ifThenElse _ cond t e = ifThenElseNP cond t e;
    ifThenElseS cond t e = SubjIfImpliesOtherwise cond t e;


    -- This is to allow lists of 'and' conjunctions to be constructed.
    -- and treated differently then cases where there is just a single 'and'.
    -- Linearize a single and without bullets.			
    -- Linearize a list of ands using bullets	
    oneAnd a b = {s0 = a.s; s1 = b.s; size = LSone};
    consAnd t a = {s0 = t.s; s1 = \\order => bulletInfix (a.s0!order) (a.s1!order); size = LSmany};	
    posAndList2Sent a = 
       case a.size of {
              LSempty => emptyS;
              LSone => ConjS AndConj (TwoS (s2S a.s0) (s2S a.s1));
              LSmany => {
			s = \\order => ((posAS allConditions).s!order ++ 
                             (wrapBullets (bulletPrefix (bulletInfix (a.s0!order) (a.s1!order)))));
			lock_S = <>
		}
       };
    negAndList2Sent a = 
       case a.size of {
              LSempty => emptyS;
              LSone => negS (ConjS AndConj (TwoS (s2S a.s0) (s2S a.s1)));
              LSmany => {
			s = \\order => ((negAS oneCondition).s!order ++ 
                             (wrapBullets (bulletPrefix (bulletInfix (a.s0!order) (a.s1!order)))));
			lock_S = <>
		}
       };
	
	
    -- For the moment, there is no special treatment for 'or' lists.
    oneOr a b = {s0 = a.s; s1 = b.s; size = LSone};
    consOr t a = {s0 = t.s; s1 = \\order => bulletInfix (a.s0!order) (a.s1!order); size = LSmany};	
    posOrList2Sent a = 
       case a.size of {
              LSempty => emptyS;
              LSone => ConjS OrConj (TwoS (s2S a.s0) (s2S a.s1));
              LSmany => { 
			s = \\order => ( (posAS oneCondition).s!order ++ 
                             (wrapBullets (bulletPrefix (bulletInfix (a.s0!order) (a.s1!order)))));
			lock_S = <>
		}
       };
    negOrList2Sent a = 
       case a.size of {
              LSempty => emptyS;
              LSone => negS (ConjS OrConj (TwoS (s2S a.s0) (s2S a.s1)));
              LSmany => { 
		s= \\order => ((negAS allConditions).s!order ++ 
                	(wrapBullets (bulletPrefix (bulletInfix (a.s0!order) (a.s1!order)))));
		lock_S = <>
	      }
       };    


--
-- Iterators
--

-- a InstIter is an instance and a list of bound variables
-- this is not abstract, we would like to simply extend Inst with 
-- a string field for the variable list. Note that Inst = NounPhrase

    instIterSingle varC _ body = {
	s1 = body.v; --v is one variable
	s = body.s; -- body is a function with some bound variables v0 ... (Str); 
	n = body.n; 
	p = body.p; 
	pro = False;
	lock_NP = <>
    };
    instIterMany varC _ body = {
	s1 = body.s1 ++ "," ++ body.v;
	s = body.s; 
	n = body.n; 
	p = body.p; 
	pro = False;
	lock_NP = <>
    };

-- a SentIter is a sentence + a list of bound variables
    sentIterSingle varC  body = {
	s1 = body.v;
	s = body.s;
	moreThanOne = False;
	lock_S = <>}
    ;
    sentIterMany varC body = {
	s1 = body.s1 ++ "," ++ body.v;
	s = body.s;
	moreThanOne = True;
	lock_S = <>
    };




--
-- Collections
--
    Collection c = mkCollClass collectionN "Collection" c;
    size _ coll = np2inst ( DefOneNP (AppFun (funGen sizeN) coll));
    includes _ _ coll elem = PredVP (inst2np coll) (PosTV containTV (inst2np elem));
    excludes _ _ coll elem = PredVP (inst2np coll) (NegTV containTV (inst2np elem));
    count _ = collCount;
    includesAll _ coll1 coll2 = PredVP (inst2np coll1) (PosTV containTV (DetNP AllDet (AppFun (funVon elementN) (inst2np coll2))));
    excludesAll _ coll1 coll2 = PredVP (inst2np coll1) (PosTV containTV (DetNP NosDet (AppFun (funVon elementN) (inst2np coll2))));
    isEmpty _ coll = (PredVP coll (PosA emptyAP));
    notEmpty _ coll = (PredVP coll (NegA emptyAP));
    sum _ coll = np2inst (DefOneNP (AppFun (funVonCN (AppFun (funGen sumN) (DefManyNP (UseN elementN)))) coll));
    forAll c coll iter = formatBlock (forAllHoldS (AdvCN (nameCN (class2cn c) iter.s1) (LocNP (inst2np coll))) (formatBlock (iter)));
    exists c coll iter = formatBlock (if_then_else (CN -> S -> S) (iter.moreThanOne)  existManyS existS (AdvCN (nameCN (class2cn c) iter.s1) (LocNP (inst2np coll))) (formatBlock (iter)));
    isUnique c d coll iter = (PredVP (appFun1 (funVon evaluationN) (inst2np iter) ) (PosTV resultTV (IndefManyNP (AdvCN (ModAdj (AdvAP (adv2ada alwaysAdV) differentAP) (UseN resultN)) (mkPP accusative "fr" (IndefManyNP (ModAdj differentAP (AdvCN (nameCN (class2cn c) iter.s1) (LocNP (inst2np coll))))))))));
    sortedBy c d coll iter = np2inst (advNP (DefOneNP (AppFun (funGen (nFrau "Reihung")) (DetNP AllDet (AdvCN (nameCN (class2cn c) iter.s1) (LocNP (inst2np coll)))))) (advAP (AdvAP (adv2ada (mkPP dative "nach" iter)) (AdjP1 (aPastPart sortV)))));
    iterate c a coll init body = np2inst (DefOneNP (ModRC (UseN resultN) (RelVP IdRP (SubjVP (PosV emergeV) IfSubj (ConjS AndConj (TwoS (OneVP (AdvVP (PosTV initializeTV (constNoInfl body.v1)) (mkPP dative "mit" (inst2np init)))) (OneVP (AdvVP (AdvVP (AdvVP (PosTV updateTV (constNoInfl body.v1)) thenAdV) (mkPP accusative "fr" (DetNP AllDet (AdvCN (nameCN (class2cn c) body.v0) (LocNP (inst2np coll)))))) (mkPP accusative "auf" (inst2np body))  )))) ))));
    any c coll iter = np2inst (DetNP irgendeinDet (ModRC (AdvCN (nameCN (class2cn c) iter.s1) (LocNP (inst2np coll))) (RelSuch iter)));
    one c coll iter = (if_then_else (CN -> S -> S) (iter.moreThanOne) (existS) (existManyS)) (ModAdj (uniqueAP) (AdvCN (nameCN (class2cn c) iter.s1) (LocNP (inst2np coll)))) (iter);
    collConforms sub super p = ss (["Collection ("] ++ (class2id sub) ++ [") ist Untertyp von Collection ("] ++ (class2id super) ++ ["), da"] ++ p.s);

--
-- sets 
--
    Set c = mkCollClass setN "Set" c;
    unionSS _ = instFunVon2 unionN;
    unionSB _ = instFunVon2 unionN;
    intersectionSS c = instFunVon2 intersectionN;
    intersectionSB c  = instFunVon2 intersectionN;
    includingS c = collIncluding setN; 
    excludingS c = collExcluding setN;
    selectSet c = collSelect setN;
    rejectSet c = collReject setN;
    collectSet c d = collCollect "Set";
    countSet _ = collCount;
    subS class a b = np2inst (ConjNP withoutConj (TwoNP a (DefManyNP (AppFun (funVon elementN) b))));
    symmetricDiff class a b = DefOneNP (AppFun (funGen setN) (DefManyNP (ModRC (AppFun (funVon elementN) (ConjNP AndConj (TwoNP a b))) (RelVP IdRP (PosVG (PredAdV (LocNP (ConjNP boldOrConj (TwoNP a b)))))))));
    setAsSequence _ s = np2inst(npAlsNP (inst2np s) (UseN sequenceN));
    setAsBag _ s = np2inst(npAlsNP (inst2np s) (UseN bagN));
    setConforms sub super p = ss (["Set ("] ++ (class2id sub) ++ [") ist Untertyp von Set ("] ++ (class2id super) ++ ["), da"] ++ p.s);
    setConforms2coll sub super elemC = ss (["Set ("] ++ (class2id sub) ++ [") ist Untertyp von Collection ("] ++ (class2id super) ++ ")");


--
-- bags
--
    Bag c = mkCollClass bagN "Bag" c;
    unionBB _ = instFunVon2 unionN; 
    unionBS _ = instFunVon2 unionN;
    intersectionBB _ = instFunVon2 intersectionN;
    intersectionBS _ = instFunVon2 intersectionN;
    includingB c = collIncluding bagN;
    excludingB c = collExcluding bagN;
    selectBag c = collSelect bagN;
    rejectBag c = collReject bagN;
    collectBag _ _ = collCollect "Bag";
    countBag _ = collCount;
    bagAsSequence _ s = np2inst(npAlsNP (inst2np s) (UseN sequenceN));
    -- In English we dont care whether it is a bag or a set
    -- Its still just a collection, so dont add any extra text.
    bagAsSet _ s = s;
    bagConforms sub super p = ss (["Bag ("] ++ (class2id sub) ++ [") ist Untertyp von Bag ("] ++ (class2id super) ++ ["), since"] ++ p.s);
    bagConforms2coll sub super elemC = ss (["Bag ("] ++ (class2id sub) ++ [") ist Untertyp von Collection ("] ++ (class2id super) ++ ")");



--
-- sequences
--
    Sequence c = mkCollClass sequenceN "Sequence" c;
    unionSeq _  = instFunVon2 unionN;
    append _ a b = np2inst (advNP (inst2np b) (advAP (AdvAP (adv2ada (mkPP accusative "an" (DefOneNP (AppFun (funVon endN) (inst2np a))))) (AdjP1 (aPastPart appendV)))));
    prepend _ a b = np2inst (advNP (inst2np b) (advAP (AdvAP (adv2ada (mkPP accusative "an" (DefOneNP (AppFun (funVon startN) (inst2np a))))) (AdjP1 (aPastPart appendV)))));
    subSequence _ s a b = np2inst (appFun1 (funVonCN (AppFun (AppFun2 (mkFun2VonBis (UseN subsequenceN)) (inst2np a)) (inst2np b))) (inst2np s));
    at _ a index = instFunVonCN ( AdvCN (UseN elementN) (Loc2NP (DefOneNP (nameCN (UseN indexN) ((inst2np index).s!NPCase nominative))))) a;
    first _  = instFunVonCN (ModAdj firstAP (UseN elementN)) ;
    last _  = instFunVonCN (ModAdj lastAP (UseN elementN)) ;
    includingSeq _ = collIncluding sequenceN;
    excludingSeq _ = collExcluding sequenceN;
    selectSeq _ = collReject sequenceN;
    rejectSeq _ = collReject sequenceN;
    collectSeq _ _ = collCollect "Sequence";
    seqAsBag _ s = np2inst(npAlsNP (inst2np s) (UseN bagN));
    -- In German we dont care whether it is a sequence or a set
    -- Its still just a collection, so dont add any extra text.
    seqAsSet _ s = s;
    seqConforms sub super p = ss (["Sequence ("] ++ (class2id sub) ++ [") ist Untertyp von Sequence ("] ++ (class2id super) ++ ["), da"] ++ p.s);
    seqConforms2coll sub super elemC = ss (["Sequence ("] ++ (class2id sub) ++ [") ist Untertyp von Collection ("] ++ (class2id super) ++ ")");

-- collection literals
lin 
    twoColl _ a b = TwoNP (inst2np a) (inst2np b);
    consColl _ x xs = ConsNP xs (inst2np x); 
    listAsSeq _ xs = listAsColl sequenceN xs;
    listAsSet _ xs = listAsColl setN xs;
    listAsBag _ xs = listAsColl bagN xs;

    emptySet _ = emptyColl setN;
    emptySeq _ = emptyColl sequenceN;
    emptyBag _ = emptyColl bagN;
    
    singletonSet _ x = singletonColl setN x;
    singletonSeq _ x = singletonColl sequenceN x;
    singletonBag _ x = singletonColl bagN x;

    rangeAsSeq f t = rangeAsColl sequenceN f t;
    rangeAsSet f t = rangeAsColl setN f t;
    rangeAsBag f t = rangeAsColl bagN f t;
    


};
