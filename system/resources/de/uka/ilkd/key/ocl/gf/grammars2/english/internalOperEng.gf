--# -path=.:../prelude:../resourceAbstract:../resourceEnglish:../resource

resource internalOperEng = open formatOCL, AtomEng, Prelude, TypesEng, ResourceEng, ResourceExtEng, ParadigmsEng, PredicationEng, myResourceExtEng, myTypesEng, LogicalEng, Predef, Prelude in {

-- operations for making classes

lintype
    SentIter = SentIterO;
    InstIter = InstIterO;

oper         

-- Constants (numerals), often used when there is no proper NL rendering
    constant : Str -> Inst = \s -> UsePN (pnReg s);  -- consider constants and numerals as proper names

    trueInst  : Inst = constant "true";
    falseInst :	Inst = constant "false";

    numeral = constant;
    numNoInfl = constNoInfl;
    
    str2Sent  : Str -> S = \t -> {s = t;lock_S = <>} ; 
    sent2str : S -> Str = \s -> s.s;
    
--    
-- Text to appear at the beginning of 'and'/'or' lists.
--

    -- "the following conditions are (not) true" 
    allConditions : AS = (mkPred 
        (DefManyNP (ModAdj followAP (UseN conditionN)))
        (PredAP trueAP) ); 
    
    -- "at least one of the following conditions is (not) true"    
    oneCondition : AS = (mkPred         
        (MassNP (AdvCN 
        (ModAdjImpl (adjNum gteAdj2 oneNum) (UseN conditionN))
        (PrepNP PartPrep (DefManyNP (ModAdj followAP (UseN conditionN))))))
        (PredAP trueAP) ); 


--
-- Formatting opers
--
    formatBlock : S -> S = \x -> {s = (mkBlock x.s); lock_S = <>};
        
--        
-- Comparison operators	    
--
       
    equalTo : Inst -> Inst -> S = \a,b ->
		predA2 equalAdj2 a b;
    notEqualTo : Inst -> Inst -> S = \a,b ->
		predNegA2 equalAdj2 a b;
    lessThan : Inst -> Inst -> S = \a,b -> -- a is less than b
	      predA2 ltAdj2 a b;
    greaterThan : Inst -> Inst -> S = \a, b -> -- a is greater than b
	      sthThan greatAdjDeg a b;
    lteThan : Inst -> Inst -> S = \a,b -> -- a is less or equal to than b
	      predA2 lteAdj2 a b;
    gteThan : Inst -> Inst -> S = \a,b -> -- a is less or equal to than b
	      predA2 gteAdj2 a b;
    sthThan : AdjDeg -> Inst -> Inst -> S = \sth, a, b -> -- a is greater than b
	      PredVP a (PosA (ComparAdjP sth b));
    ofType : Inst -> Inst -> S = \a,b -> -- a is of type b
	      predA2 typeAdj2 a b;

--
--  Collections
--

-- general operations

    collCount : Inst -> Inst -> Inst = \coll, elem ->
        np2inst (DefOneNP (
            AppFun (mkFunCN 
                (AppFun 
                    (funOfCN (AppFun (funGenCN (UseN numberN)) (IndefNumNP NoNum ( UseN  occurrenceN))))
                    elem
                ) 
                "in")
            (inst2np coll))
        );
    collCollect : Str -> Inst -> InstIterL -> Inst = \collType, coll, iter -> 
	(DefOneNP (AdvCN (AppFun (funOfCN (UseN collectionN)) (inst2np iter)) (forNP (DetNP AllDet (AdvCN (const2CN iter.s1) (LocNP (inst2np coll)))))));
    collIncluding : N -> Inst -> Inst -> Inst = \collType, coll, elem -> 
	np2inst (DefOneNP (ModRC (UseN collType) (RelVP IdRP (PosTV containTV (ConjNP AndConj (TwoNP (DetNP AllDet (AppFun (funOfCN (UseN elementN)) (inst2np coll))) (inst2np elem)))))));
    collExcluding : N -> Inst -> Inst -> Inst = \collType, coll, elem -> 
	np2inst (DefOneNP (ModRC (UseN collType) (RelVP IdRP (PosTV containTV (ConjNP withoutConj (TwoNP (DetNP AllDet (AppFun (funOfCN (UseN elementN)) (inst2np coll))) (inst2np elem)))))));
    collSelect : N -> Inst -> SentIter -> Inst = \collType, coll, iter -> 
	np2inst (DefOneNP (AppFun( funGenCN (AppFun (funGen collType) (DetNP AllDet (ModRC (nameCN (UseN elementN) iter.s1) (RelSuch iter))))) (inst2np coll)));
    collReject : N -> Inst -> SentIter -> Inst = \collType, coll, iter -> 
	np2inst (appFun1 (funGen collType) (DetNP AllDet (ModRC (AppFun (funOfCN (nameCN (UseN elementN) iter.s1)) (inst2np coll)) (RelSuch (negS iter)))));
	
-- collection literals

    listAsColl : N -> ListNP -> Inst = \collN, list -> np2inst (
        DefOneNP (ModRC
            (UseN collN)
            (RelVP IdRP (PosVG (PredTV
                  containTV
                  (ConjNP AndConj list)
             ))))    
    );
    
    emptyColl : N -> Inst = \collN -> np2inst (DefOneNP (ModAdj emptyAP (UseN collN))); 
    
    -- maybe add "as its single element" or something similar to this:
    singletonColl : N -> Inst -> Inst = \collN, x -> np2inst (
        DefOneNP (ModRC
            (UseN collN)
            (RelVP IdRP (PosVG (PredTV
                  containTV
                  (inst2np x)
             ))))    
    );
    
    rangeAsColl : N -> Inst -> Inst -> Inst = \collN, f, t -> np2inst ( 
        -- the collN of integers from f to t
        (appFun1 (mkFun collN "of") (IndefNumNP NoNum (AppFun (AppFun2 (mkFun2VonBis (UseN integerN)) (inst2np f)) (inst2np t))))
    );

-- This is lower level stuff
    
    inst2str : Inst -> Str = \i -> (inst2np i).s ! NomP;
    
    
    constNoInfl : Str -> Inst = \str ->  { 
	s = table {
		GenP => str; -- nonExist;
		GenSP => str; -- nonExist;
		_ => str
	};
	n = Sg; 
	p=P3;
	lock_NP = <>
    };
--    const2CN	: Str -> CN = \str -> { 
--	s = \\_ => \\_ => table { 
--		Gen => nonExist; 
--		_ => str}; 
--	g = nonhuman};
    const2CN : Str -> CN = \stri ->
	UseN (mkN stri stri nonExist nonExist nonhuman);

    instInfix : Str -> Inst -> Inst -> Inst = \plus, a, b -> np2inst ( {
		s = table {
		    -- should GenP/GenSP forms exist? We need them at least because of two-place functions like
		    -- subsequence from x to y (for y). 
			-- GenP => nonExist;
			-- GenSP => nonExist;
			c   => a.s!c ++ plus ++ b.s!c
		};
		n = Sg; 
		p = P3;
		lock_NP = <>
	} );
    instPrefix : Str -> Inst -> Inst = \not, a -> np2inst ( { 
	s = table {
	        -- see comment above:
			-- GenP => nonExist;
			-- GenSP => nonExist;
			c => not ++ a.s!c
		};
	n = (inst2np a).n;
	p = (inst2np a).p;
	lock_NP = <>
	});


--
-- Utility opers for classes, attributes and operations.
--    

    class2id : ClassL -> Str = \c -> mkCode c.s42;
    class2cn : ClassL -> CN = \c -> {s = c.s; g = c.g; lock_CN = <>};          
    emptyS  : S = {s = "";lock_S = <>} ;
    inst2str : Inst -> Str = \i -> (inst2np i).s!NomP;

-- one- or two-place functions ("Gr�e von", "Summe von"), also infix/pre(query ++ "(" ++ args.s ++ ")")fix  
    instFunVon : N -> Inst -> Inst = \size, object ->
	    instFunVonCN (UseN size) object;
    instFunVonCN : CN -> Inst -> Inst = \size, object ->
	    np2inst (DefOneNP (AppFun (funOfCN size) (inst2np object)));
    instFunVon2 : N -> Inst -> Inst -> Inst = \maximum, a, b ->
	    DefOneNP (appFamColl (funOfCN (UseN maximum)) a b);
    instFunOnCN : CN -> Inst -> Inst = \query, object ->
	    np2inst (appFun1 (mkFunCN query "on") (inst2np object));
    instFunOn : N -> Inst -> Inst = \query, object ->
	    instFunOnCN (UseN query) object;


--
-- Utility opers for constraints.
-- These opers should be used internally in the OCL GF grammar to build up the constraint
-- text from its constituent parts.
--
    
    
    -- Create a sentence adverbial for a class.
    -- I.e. "for the class x"
    classAdV : N -> Str -> AdV = \type, name ->
        (forNP (DefOneNP (nameCN (UseN type) (mkBold name))));
    
    -- Create a sentence adverbial for an operation.
    -- I.e. "for the operation x of the class y"    
    opAdV : N -> Str -> Str -> AdV = \type, op, class -> mapStr AdV capitalize
        (forNP (appFun1
        (funOfCN (nameCN (UseN type) (mkBold op)))
        (DefOneNP (nameCN (UseN classN) (mkBold class)))
        ));                         
                 
    -- Turns the ConstraintBody in to a sentence.
--     cb2s : ConstraintBodyL -> S = 
-- 	    \cb -> convertConstraint cb (hasInv cb) (hasInvAndCond cb) (hasPreAndPost cb);

    -- Turns the ConstraintBody in to a sentence, adding some puntutations.
    -- For use with operation constraints.
--     cb2s' : ConstraintBodyL -> S = \body ->
--         PrePunctuate comma (PrePunctuate mkLineBreak (cb2s body));

    classCB2s : ClassConstraintBodyL -> S = \ccb -> case ccb.invC of {
        E0 => -- no invariants
            extractDef ccb;
        _ => case ccb.defC of {
            E0 => -- no defs
                extractInv ccb;
            _ => ConjS AndConj (TwoS (extractDef ccb) (extractInv ccb))
        }
    };
    
    -- this breaks if there are preconditions but no postconditions:
    operCB2s : OperConstraintBodyL -> S = \opcb -> PrePunctuate comma (
        PrePunctuate mkLineBreak (case opcb.preC of {
            E0 => -- no preconditions
                extractPost opcb;
            _ => SubjThen givenSubj (extractPre opcb) (extractPost opcb)
        })
    );

    -- Converts the ConstraintBody in to a sentence.
    -- A different sentence is produced depending on whether or not the constraint
    -- contains invariants, preconditions or postconditions.
--     convertConstraint : ConstraintBodyL -> Bool -> Bool -> Bool -> S =
--         \cb, ibool, icbool, ppbool -> 
--         case cb.isDef of {
--             False => (case icbool of {
--                 True => ConjS AndConj (TwoS (extractInv cb) (convertPrePost cb ppbool));
--                 False => 
--                     (case ibool of {
--                         True => extractInv cb;
--                         False => convertPrePost cb ppbool
--                     })        
--             });
--             True => {s=cb.s0; lock_S = <>} -- FIXME!
--         };
--                 
--     -- Converts the pre and post condtions of a constraint body into a sentence.
--     convertPrePost : ConstraintBodyL -> Bool -> S =
--         \cb, ppbool -> (case ppbool of {
--                 True => SubjThen givenSubj (extractPre cb) (extractPost cb);
--                 False => extractPost cb});
                
    
    -- Extract the invariant from the constraint body
    extractInv : ClassConstraintBodyL -> S = 
	\cb -> (case cb.invC of {
		 E0 => emptyS;
		 E1 => structureConstraint (invIntro Sg) cb.s0;                
		 _ => structureConstraint (invIntro Pl) cb.s0
	});
	
	extractDef : ClassConstraintBodyL -> S = \cb -> case cb.defC of {
	   E0 => emptyS;
	   E1 => structureConstraint (defIntro Sg) cb.s1;
	   _  => structureConstraint (defIntro Pl) cb.s1
	};
 
    -- Extract the precondition from the constraint body
    extractPre : OperConstraintBodyL -> S = 
	\cb -> (case cb.preC of {
		E0 => emptyS;
		E1 => structureConstraint (preIntro Sg) cb.s0;                
		_ => structureConstraint (preIntro Pl) cb.s0
	});
 
    -- Extract the postcondition from the constraint body
    extractPost : OperConstraintBodyL -> S = 
	\cb -> (case cb.postC of {
		E0 => emptyS;
		E1 => structureConstraint (postIntro Sg) cb.s1;                
		_ => structureConstraint (postIntro Pl) cb.s1
	});             
    
    -- Take a constraint introduction text and places it before the
    -- formatted constraint body.
    structureConstraint : S -> Str -> S = \intro, body ->
		PostPunctuate (PostPunctuate intro colon) (wrapBullets body);    
              
    -- Gives a result of True if the constraint contains an invariant.
--     hasInv : ConstraintBodyL -> Bool = \cb -> LS2Bool ! cb.invC;

    -- Gives a result of True if the constraint contains either (an invariant and
    -- precondition) OR (an invariant and postcondition)
--     hasInvAndCond : ConstraintBodyL -> Bool = \cb ->
--         hasInvAndCond' (LS2Bool ! cb.invC) (LS2Bool ! cb.preC) (LS2Bool ! cb.postC);
--     hasInvAndCond' : (b1,b2,b2 : Bool) -> Bool = \b1, b2, b3 ->
-- 	    if_then_else Bool (orB (andB b1 b2) (andB b1 b3)) True False;
	    
    -- Gives a result of True if the constraint contains both a pre and a post condition.
--     hasPreAndPost : ConstraintBodyL -> Bool = \cb ->
-- 	    hasPreAndPost' (LS2Bool ! cb.preC) (LS2Bool ! cb.postC);
--     hasPreAndPost' : (b2,b3 : Bool) -> Bool = \b2, b3 ->
-- 	    if_then_else Bool (andB b2 b3) True False;

	    
    -- Constructs the introduction text for an invariant.
    -- I.e. "the following invariant holds"
    invIntro : Number -> S = \num -> case num of {
        Sg => (PredVP 
                (DefOneNP (ModAdj followAP (UseN invariantN)))
                (PosVG (PredV holdV)));
        Pl => (PredVP 
                (DefManyNP (ModAdj followAP (UseN invariantN)))
                (PosVG (PredV holdV)))
        };
    
    -- Constructs the introduction text for definitions.
    -- "introduce the following definition(s)"
    -- FIXME: use resource grammars!
    -- for imperatives, we need to use Phr (phrases) instead of S,
    defIntro : Number -> S = \num -> case num of {
        Sg => {s = ["introduce the following definition"]; lock_S = <>};
        Pl => {s = ["introduce the following definitions"]; lock_S = <>}
    };
    
    -- Constructs the introduction text for a precondition.
    -- I.e. "given the following precondition"    
    preIntro : Number -> S = \num -> case num of {
        Sg => np2s (DefOneNP (ModAdj followAP (UseN preconditionN)));                
        Pl => np2s (DefManyNP (ModAdj followAP (UseN preconditionN)))
        };
        
    -- Constructs the introduction text for a postcondition.
    -- I.e. "the following postcondition holds"
    postIntro : Number -> S = \num -> case num of {
        Sg => (PredVP 
                (DefOneNP (ModAdj followAP (UseN postconditionN)))
                (PosVG (PredVV shouldVV (PredV holdV))));
        Pl => (PredVP 
                (DefManyNP (ModAdj followAP (UseN postconditionN)))
                (PosVG (PredVV shouldVV (PredV holdV))))
        };        
        

--
-- let-definitions
--
oper letNoArg : Inst -> Inst -> LetDefL = \i1, i2 -> 
        {s0 = inst2str i1; s1 = inst2str i2};
    letNoArgSent : S -> S -> LetDefSentL = \sent1, sent2 -> 
        {s0 = sent1.s; s1 = sent2.s};

--
-- Miscellaneous opers
--
        
    LSsucc : ListSize => ListSize = table {LSempty => LSone; LSone => LSmany; LSmany => LSmany};
    LS2Bool : ListSize => Bool = table {LSempty => False; _ => True};

};
