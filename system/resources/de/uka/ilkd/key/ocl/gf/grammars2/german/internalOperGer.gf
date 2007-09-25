--# -path=.:../prelude:../resourceAbstract:../resource:../resourceGerman

resource internalOperGer = open Prelude, TypesGer, ResourceGer, ParadigmsGer,
    PredicationGer, myResourceExtGer, myTypesGer, ResourceExtGer, formatOCL, AtomGer
    in {

-- operations for making classes

lintype
    SentIter = SentIterO;
    InstIter = InstIterO;

oper 


-- Constants (numerals), often used when there is no proper NL rendering
    constant : Str -> Inst = \s -> UsePN (pnReg s);  -- consider constants and numerals as proper names

    trueInst  : Inst = constant "wahr";
    falseInst :	Inst = constant "falsch";

    numeral = constant;
    numNoInfl = constNoInfl;

    str2Sent  : Str -> S = \t -> {s = \\_ => t;lock_S = <>} ; --%%

--    
-- Text to appear at the beginning of 'and'/'or' lists.
--

    -- "the following conditions are (not) true" 
    allConditions : AS = (mkPred 
        (DefManyNP (ModAdj followAP (UseN conditionN)))
        (PredAP trueAP) ); 
    
    -- "at least one of the following conditions is (not) true"    
    oneCondition : AS = (mkPred
		   (atLeastOneOfTheNP (ModAdj followAP (UseN conditionN)))
		   (PredAP trueAP) ); 

--
-- Formatting opers
--
    formatBlock : S -> S = \x -> {s = \\order => (mkBlock ((x.s)!order)); lock_S = <>};

-- Comparison operators
-- some sthThan in here &&
    equalTo : Inst -> Inst -> S = \a,b ->
		predA2 equalAdj2 a b;
    notEqualTo : Inst -> Inst -> S = \a,b ->
		predNegA2 equalAdj2 a b;
    lessThan : Inst -> Inst -> S = \a,b -> -- a is less than b
	      sthThan littleAdjDeg a b;
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
     	        np2inst (DefOneNP (AppFun (mkFunCN (AppFun (funVonCN (AppFun (funGenCN (UseN amountN)) (IndefManyNP ( UseN  occurrenceN)))) elem) (mkPrep "in" Dat)) (inst2np coll)));
    collCollect : Str -> Inst -> InstIterL -> Inst = \collType, coll, iter -> 
	(DefOneNP (AdvCN (AppFun (funVonCN (UseN collectionN)) (inst2np iter)) (forNP (DetNP AllDet (AdvCN (const2CN iter.s1) (LocNP (inst2np coll)))))));
    collIncluding : N -> Inst -> Inst -> Inst = \collType, coll, elem ->
	np2inst (DefOneNP (ModRC (UseN collType) (RelVP IdRP (PosTV containTV (ConjNP AndConj (TwoNP (DetNP AllDet (AppFun (funVonCN (UseN elementN)) (inst2np coll))) (inst2np elem)))))));
    collExcluding : N -> Inst -> Inst -> Inst = \collType, coll, elem -> 
	np2inst (DefOneNP (ModRC (UseN collType) (RelVP IdRP (PosTV containTV (ConjNP withoutConj (TwoNP (DetNP AllDet (AppFun (funVonCN (UseN elementN)) (inst2np coll))) (inst2np elem)))))));
    collSelect : N -> Inst -> SentIter -> Inst = \collType, coll, iter -> 
	np2inst (DefOneNP (AppFun( funGenCN (AppFun (funGen collType) (DetNP AllDet (ModRC (nameCN (UseN elementN) iter.s1) (RelSuch iter))))) (inst2np coll)));
    collReject : N -> Inst -> SentIter -> Inst = \collType, coll, iter -> 
	np2inst (appFun1 (funGen collType) (DetNP AllDet (ModRC (AppFun (funVonCN (nameCN (UseN elementN) iter.s1)) (inst2np coll)) (RelSuch (negS iter)))));

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
        (appFun1 (mkFun collN (mkPrep "der" genitive)) (IndefNumNP NoNum (AppFun (AppFun2 (mkFun2VonBis (UseN integerN)) (inst2np f)) (inst2np t))))
    );


-- This is lower level stuff

    constNoInfl : Str -> Inst = \str ->  { 
	s = table {
		_ => str
	};
	n = Sg; p=P3; pro=False; lock_NP = <>
    };
--    const2CN	: Str -> CN = \str -> { 
--	s = \\_ => \\_ => table { 
--		Gen => nonExist; 
--		_ => str}; 
--	g = neuter;
--	lock_CN = <>
--	};
    const2CN : Str -> CN = \str ->
	UseN (mkN str str str str "const2CN" "const2CN" neuter);
    instInfix : Str -> Inst -> Inst -> Inst = \plus, a, b -> np2inst ( {
		s = table {
			NPCase Gen => nonExist;
			NPCase c   => a.s!NPCase c ++ plus ++ b.s!NPCase c;
			_ 	   => nonExist
		};
		n = Sg; 
		p = P3;
		pro = False;
		lock_NP = <>
	} );
    instPrefix : Str -> Inst -> Inst = \not, a -> np2inst ( { 
	s = table {
			NPCase Gen => nonExist;
			NPCase c => not ++ a.s! NPCase c;
			_ => nonExist
		};
	n = (inst2np a).n;
	p = (inst2np a).p;
	pro = False;
	lock_NP = <>
	});

--
-- Utility opers for classes, attributes and operations.
--    

    class2id : ClassL -> Str = \c -> mkCode c.s42;
    class2cn : ClassL -> CN = \c -> {s = c.s; g = c.g; lock_CN = <>};          
    emptyS  : S = {s = \\order => "";lock_S = <>} ;
    inst2str : Inst -> Str = \i -> (inst2np i).s!NPCase nominative;

-- one- or two-place functions ("Gr�e von", "Summe von"), also infix/pre(query ++ "(" ++ args.s ++ ")")fix  
    instFunVon : N -> Inst -> Inst = \size, object ->
	    instFunVonCN (UseN size) object;
    instFunVonCN : CN -> Inst -> Inst = \size, object ->
	    np2inst (DefOneNP (AppFun (funVonCN size) (inst2np object)));
    instFunVon2 : N -> Inst -> Inst -> Inst = \maximum, a, b ->
	    DefOneNP (appFamColl (funVonCN (UseN maximum)) a b);
    instFunAnCN : CN -> Inst -> Inst = \query, object ->
	    np2inst (appFun1 (mkFunCN query (mkPrep "an" accusative)) (inst2np object));
    instFunAn : N -> Inst -> Inst = \query, object ->
	    instFunAnCN (UseN query) object;


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
    opAdV : N -> Str -> Str -> AdV = \type, op, class ->
        (forNP (appFun1
        (funGenCN (nameCN (UseN type) (mkBold op)))
        (DefOneNP (nameCN (UseN classN) (mkBold class)))
        ));                         

    --Fuer ... sind die folgenden Vorbedingungen erfuellt
    preHoldS : Number -> AdV -> S = \num , forop ->
		PredVP  (case num of {
	            Sg =>  (DefOneNP (ModAdj followAP (UseN preconditionN)));                
        	    Pl =>  (DefManyNP (ModAdj followAP (UseN preconditionN)))
	        }) (PosA (AdvAP (adv2ada forop) (AdjP1 fullfilledAdj1)))  ;

    --prints out preconditions and preconditions
    putPreAndPost : AdV -> OperConstraintBodyL -> S = \op, opcb ->
	ifThenS (structureConstraint (preHoldS (case opcb.preC of {E1 => Sg; _ => Pl}) op)  (opcb.s0) )(putPost (mkAdV "") opcb);


    -- Extract the postcondition from the constraint body
    putPost : AdV -> OperConstraintBodyL -> S = 
	\op, cb -> (case cb.postC of {
		E0 => emptyS;
		E1 => structureConstraint (postconditionsShouldHoldS Sg op) cb.s1;                
		_ => structureConstraint (postconditionsShouldHoldS Pl op) cb.s1
	});             


    -- Constructs the introduction text for a postcondition.
    -- I.e. "the following postcondition holds"
    postconditionsShouldHoldS : Number -> AdV -> S = \num, op -> case num of {
        Sg => (PredVP 
                (DefOneNP (ModAdj followAP (UseN postconditionN)))
                (AdvVP (PosVG (PredVV shouldVV (PredV holdV))) op));
        Pl => (PredVP 
                (DefManyNP (ModAdj followAP (UseN postconditionN)))
                (AdvVP (PosVG (PredVV shouldVV (PredV holdV))) op))
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



    -- Extract the postcondition from the constraint body
    extractPost : OperConstraintBodyL -> S = 
	\cb -> (case cb.postC of {
		E0 => emptyS;
		E1 => structureConstraint (postIntro Sg) cb.s1;                
		_ => structureConstraint (postIntro Pl) cb.s1
	});             
	

--PredVP x (PosA (AdjP1 F))
--
-- constraints
-- mostly directly from the English grammar... we might want to extract common 
-- parts...

    classCB2s : ClassConstraintBodyL -> S = \ccb -> case ccb.invC of {
        E0 => -- no invariants
            extractDef ccb;
        _ => case ccb.defC of {
            E0 => -- no defs
                extractInv ccb;
            _ => ConjS AndConj (TwoS (extractDef ccb) (extractInv ccb))
        }
    };
    
    -- this breaks if there are preconditions but no postconditions: (really, and even if, is that possible?)
    operCB2s : AdV -> OperConstraintBodyL -> S = \op, opcb -> 
	PrePunctuate mkLineBreak (case opcb.preC of {
		E0  => putPost op opcb;
		_ => putPreAndPost op opcb

	});



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
 
    
    -- Take a constraint introduction text and places it before the
    -- formatted constraint body.
    structureConstraint : S -> Str -> S = \intro, body ->
		PostPunctuate (PostPunctuate intro colon) (wrapBullets body);   
		
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
        Sg => {
		s = table {
			Main => "fuehre folgende Vereinbarung ein";
			Inv  => "fuehre folgende Vereinbarung ein";
			Sub  => "fuehre folgende Vereinbarung ein"
		};
		lock_S = <>
	};
        Pl => {s = \\o => "fuehre folgende Vereinbarungen ein"; lock_S = <>}
    };
    
    -- Constructs the introduction text for a precondition.
    -- I.e. " given the following precondition"    
    preIntro : Number -> S = \num -> {s = table {_ =>
        "gegeben" ++ 
        (case num of {
            Sg =>  (DefOneNP (ModAdj followAP (UseN preconditionN)));                
            Pl =>  (DefManyNP (ModAdj followAP (UseN preconditionN)))
            }).s ! NPCase Nom};
        lock_S = <>};
        

--
-- let-definitions
--
oper letNoArg : Inst -> Inst -> LetDefL = \i1, i2 -> 
        {s0 = inst2str i1; s1 = inst2str i2};
    letNoArgSent : S -> S -> LetDefSentL = \sent1, sent2 -> 
        {s0 = sent1.s!Main; s1 = sent2.s!Main};

--
-- Miscellaneous opers
--
        
    LSsucc : ListSize => ListSize = table {LSempty => LSone; LSone => LSmany; LSmany => LSmany};
    LS2Bool : ListSize => Bool = table {LSempty => False; _ => True};
  
-- bulletInfix in format only takes Str as arguments, sth, which is not sufficient in German.
    bulletInfixS : S -> S -> S = \a,b -> {
	s = \\order => bulletInfix  (a.s!order)  (b.s!order);
	lock_S = <>
    };

};
