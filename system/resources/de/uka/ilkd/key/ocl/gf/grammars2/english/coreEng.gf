--# -path=.:../prelude:../resourceAbstract:../resourceEnglish:../resource:../abstract
concrete coreEng of core =  open 
    Prelude,
    formatOCL, internalOperEng, myTypesEng, myResourceExtEng, PropsAndPredsEng,
    AtomEng, ResourceEng,  externalOperEng, AtomEng, ResourceEng,  ParadigmsEng, 
    PredicationEng, ExtraEng, TypesEng in {


lincat 
    Class = ClassL;
    Sent = S;
    AtomSent = AS;
    Instance = Inst;
--    CoercedTo = Inst;
    Subtype = SubtypeL;
    ClassConstraintBody = ClassConstraintBodyL;
    OperConstraintBody = OperConstraintBodyL;
    SentIter = SentIterL;
    InstIter = InstIterL;
    Constraints = ConstraintL;
    Document = DocumentL;
    AndList = AndListL;
    OrList = OrListL;
    SumList = SumListL;
    ProductList = SumListL;
    LetDef = LetDefL;
    LetDefSent = LetDefSentL;
    LetDefList = LetDefListL;
    CollList = ListNP;
--
-- Properties
--
    Property = PropertyL;
    Predicate = PredicateL;
    
    
printname
    coerce = "[upcast]";


lindef Instance = \str -> constNoInfl (mkItalic str);
-- lindef CoercedTo = \str -> constNoInfl (mkItalic str);

lin

--
-- Sentences 
--
    atPreSent : S -> S = \s ->
	{
		s = s.s ++ ["at the begin of the operation"]; 
		lock_S = <>
	}; -- This is a cheat! Solution depends on Sentences consisting of their parts which would be huge change to the resource grammars

    negAtom a = negAS a;
    posAtom a = posAS a;
    
--
-- Subtyping 
--
    coerce sub super proof obj = obj;
--     subTypeTrans : (a, b, c : ClassL) -> SubtypeL -> SubtypeL -> SubtypeL = 
-- 	\a, b, c, pab, pbc -> {s = ["Every"] ++ (getNomSgCN a) ++ ["is a"] ++ (getNomSgCN c) ++ "," 
--     	++ ["because of"] ++ pab.s ++ "and" ++ pbc.s}; 
--     subTypeRefl : (c : ClassL) -> SubtypeL = \a -> {s = "a" ++ (getNomSgCN a) ++ ["is a"] ++ (getNomSgCN a)};  


--
-- Instances
--

    eq _  = equalTo;
    neq _ = notEqualTo;	
    atPre _ i = np2inst (appFun1 (funOfCN (ModAdj previousAP (UseN valueN))) (inst2np i));

--
-- self & result
--
    self c _ = np2inst (DetNP ThisDet (class2cn c));
    result _ _ = np2inst (DefOneNP (UseN resultN));


--
-- pre- and postconditions
--


    emptyOperC = {s0,s1 = ""; preC, postC = E0};
    emptyClassC = {s0,s1 = ""; invC, defC = E0};
    emptyPostC = PredVP (DefOneNP (UseN operationN)) (AdvVP (PosVG (PredV terminateV)) normallyAdV);
    
-- The following are cheats, they use Types and are just Str, no Sentence

    defC _ ld cs = {
        s0 = cs.s0;
        s1 = mkBullet ++ ld.s0 ++ ["is defined as"] ++ ld.s1 ++ cs.s1;
        invC = cs.invC;
        defC = eNext cs.defC};
    defSentC ld cs = {
        s0 = cs.s0;
        s1 = mkBullet ++ ld.s0 ++ ["if and only if"] ++ ld.s1 ++ cs.s1;
        invC = cs.invC;
        defC = eNext cs.defC};
    invC i cs = 
        {s0 = mkBullet ++ i.s ++ cs.s0; 
         invC = eNext cs.invC;
         s1 = cs.s1; defC = cs.defC;
        };
    invCt i  = {
	s0 = i.s; 
        invC = E1;
        s1 = "";
	defC = E0;
    };

    preC p cs = 
        {s0 = mkBullet ++ p.s ++ cs.s0; 
         s1 = cs.s1; 
         preC = eNext cs.preC; 
         postC = cs.postC;
        };
    postC p cs = 
        {s0 = cs.s0; 
         s1 = mkBullet ++ p.s ++ cs.s1; 
         preC = cs.preC;
         postC = eNext cs.postC;
        };
    prepostCt precond postcond = 
        {s0 = precond.s; 
         s1 = postcond.s; 
         preC = E1;
         postC = E1;
        };


        
    invHC s = {s = s.s};


--
-- let-definitions
--
lin 

    letProperty rec ret prop definiens = letNoArg
        -- (np2inst (DefOneNP (prop2cn prop)))
        (implPropCallO (inst2np (IndefOneNP (class2cn rec))) prop)
        definiens;

    letPredicate rec pred definiens = letNoArgSent
        (posAS (predCallO (inst2np (IndefOneNP (class2cn rec))) pred))
        definiens;

     letAddArg c d boundLetDef = boundLetDef;
     letAddArgSent c boundLetDefSent = boundLetDefSent;

    
    typeFormalParam clss exp = exp; -- has effect only in OCL


    nilLet = {s= ""; length = E0};
    consLet _ ld lds = {
        s = (mkBullet ++ ld.s0 ++ ["is defined as"] ++ ld.s1 ++ lds.s);
        length = eNext lds.length
    };
    consLetSent ld lds = {
        s = (mkBullet ++ ld.s0 ++ ["if and only if"] ++ ld.s1 ++ lds.s);
        length = eNext lds.length
    };
    
    localLet letdefs sent = -- FIXME:
        ss (["Use the following"] ++
            (case letdefs.length of {E1 => "definition"; _ => "definitions"}) ++ 
            wrapBullets letdefs.s ++ ["in:"] ++ sent.s) 
        ** {lock_S=<>};

--
-- list of constraints
-- 

    oneConstraint c = c;
    consConstraint c cs = {s = c.s ++ mkDivide ++ cs.s};
    document cs = {s = (mkFormatHeader (mkTitle ("OCL" ++ "Constraints"))
        (mkHeading ("OCL" ++ "Constraints")) (mkStyle "OCLstyle.css"))
        ++ cs.s ++ mkFormatFooter};

--
-- Properties
--
    propCall _ _ = propCallO;
    implPropCall _ _ = implPropCallO;
    predCall _ = predCallO;
    implPredCall _ = implPredCallO;

{-
--
-- lists of instances
--
lincat InstList = InstListL;

lin twoInst _ a b = {
        s0 = \\npf => (inst2np a).s!npf;
        s1 = \\npf => (inst2np b).s!npf
    };
    
    consInst _ x xs = {
        s0 = \\npf => (inst2np x).s!npf ++ "," ++ xs.s0!npf;
        s1 = \\npf =>  xs.s1!npf
    };

    instList2andInst _ xs = np2inst ({
        s = \\npf => xs.s0!npf ++ "and" ++ xs.s1!npf;
        n = Pl;
        p = P3; 
        lock_NP = <>
    });

    instList2orInst _ xs = np2inst ({
        s = \\npf => xs.s0!npf ++ "or" ++ xs.s1!npf;
        n = Pl;
        p = P3; 
        lock_NP = <>
    });
-}
};
