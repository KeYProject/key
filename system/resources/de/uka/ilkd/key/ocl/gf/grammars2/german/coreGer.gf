--# -path=.:../resourceAbstract:../prelude:../resourceGerman:../abstract:../resource
--# -optimize=all
concrete coreGer of core =  open Prelude, 
    TypesGer, ResourceGer, ParadigmsGer, PredicationGer, ResourceExtGer, 
    ExtraGer, AtomGer,
    internalOperGer, myTypesGer, myResourceExtGer, externalOperGer, 
    PropsAndPredsGer,
    formatOCL in {

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
    Property = PropertyL;
    Predicate = PredicateL;



printname
    coerce = ["[in Obertyp umwandeln]"];

lindef Instance = \str -> constNoInfl (mkItalic str);


--
-- Sentences 
--
lin atPreSent s = {s = (table{ c => s.s!c ++ ["zum Beginn der Operation"]}); lock_S = <>}; -- This is a cheat! Solution depends on Sentences consisting of their parts which would be huge change to the resource grammars

    negAtom a = negAS a;
    posAtom a = posAS a;


--
-- Subtyping 
--
    coerce sub super proof obj = obj;
--     subTypeTrans a b c pab pbc = {s = ["Jedes"] ++ a.s!Weak!Sg!Nom ++ ["ist ein"] ++ c.s!Weak!Sg!Nom ++ "," 
--     	++ "da" ++ pab.s ++ "und" ++ pbc.s}; 
--     subTypeRefl a = {s = "ein" ++ a.s!Weak!Sg!Nom ++ ["ist ein"] ++ a.s!Weak!Sg!Nom};  


--
-- Instances
--

    eq _  = equalTo;
    neq _ = notEqualTo;	
    atPre _ i = np2inst (appFun1 (funVonCN (ModAdj previousAP (UseN valueN))) 
                                 (inst2np i)
                        );

--
-- self & result
--
    self c _ = np2inst (DefOneNP (class2cn c));
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
        s1 = mkBullet ++ ld.s0 ++ ["ist definiert als"] ++ ld.s1 ++ cs.s1;
        invC = cs.invC;
        defC = eNext cs.defC};
    defSentC ld cs = {
        s0 = cs.s0;
        s1 = mkBullet ++ ld.s0 ++ ["genau dann wenn"] ++ ld.s1 ++ cs.s1;
        invC = cs.invC;
        defC = eNext cs.defC};
    invC i cs = {
	s0 = mkBullet ++ i.s!Main ++ cs.s0; 
        invC = eNext cs.invC;
        s1 = cs.s1; 
	defC = cs.defC;
    };
    invCt i  = {
	s0 = i.s!Main; 
        invC = E1;
        s1 = "";
	defC = E0;
    };

    preC p cs = 
        {s0 = mkBullet ++ p.s!Main ++ cs.s0; 
         s1 = cs.s1; 
         preC = eNext cs.preC; 
         postC = cs.postC;
        };
    postC p cs = 
        {s0 = cs.s0; 
         s1 = mkBullet ++ p.s!Main ++ cs.s1; 
         preC = cs.preC;
         postC = eNext cs.postC;
        };
    prepostCt precond postcond = 
        {s0 = precond.s!Main;
         s1 = postcond.s!Main;
         preC = E1;
         postC = E1;
        };
        
    invHC s = {s = s.s!Main};

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
        s = (mkBullet ++ ld.s0 ++ ["ist definiert als"] ++ ld.s1 ++ lds.s);
        length = eNext lds.length
    };
    consLetSent ld lds = {
        s = (mkBullet ++ ld.s0 ++ ["genau dann wenn"] ++ ld.s1 ++ lds.s);
        length = eNext lds.length
    };
    
    localLet letdefs sent = { -- FIXME:
	s = table {
		Main => ((case letdefs.length of {
				E1 => ["Benutze die folgende Definition"]; 
				_ => ["Benutze die folgenden Definitions"]}
			)
			++ wrapBullets letdefs.s ++ ["in:"] ++ sent.s!Main);
		_ =>	nonExist
	};
	lock_S=<>
    };


--
-- list of constraints
-- 

    oneConstraint c = c;
    consConstraint c cs = {s = c.s ++ mkDivide ++ cs.s};
    document cs = {s = (mkFormatHeader (mkTitle ("OCL" ++ "Constraints"))
        (mkHeading ("OCL" ++ "Constraints")) (mkStyle "OCLstyle.css"))
        ++ cs.s ++ mkFormatFooter};

--
-- Properties & Predicates
--

    propCall _ _ rec prop = propCallO rec prop;
    implPropCall _ _ rec prop = implPropCallO rec prop;
    
    predCall _ rec pred = predCallO rec pred;
    implPredCall _ rec pred = implPredCallO rec pred;


{-
-- use any string as an attribute/operation, hoping that it has
-- been defined somewhere using a let-expression
-- (no type checking here...)

    useLetDef _ _ name obj args = mkQuery obj name.s args;
    useLetArgNil = argNil; -- {s = ""; isNil = True};
    useLetArgCons c = argCons; 

-}

};
