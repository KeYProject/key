--# -path=.:../prelude:../resourceAbstract:../resourceGerman

resource PropsAndPredsGer = open Prelude, TypesGer, ResourceGer, 
    ParadigmsGer, PredicationGer, AtomGer, MorphoGer,
    myTypesGer, internalOperGer, myResourceExtGer in { -- 


--
-- Properties
--
param PropType = SimpleProperty | OnProperty  | StaticProperty | AssocProperty;

lintype
    PropertyL  =  -- {s:CN; pt : PropType}
        CN ** {pt : PropType};

oper 
    prop2cn : PropertyL -> CN = \p -> p;
    cn2prop : PropType -> CN -> PropertyL = \pt,cn -> 
        cn ** {pt = pt};

    propCallO : Inst -> PropertyL -> Inst = \rec, prop -> case prop.pt of {
        SimpleProperty => -- "the prop of the rec"
            np2inst (appFun1 (funGenCN prop) rec);
        OnProperty => -- "the prop on obj"
            instFunAnCN prop rec;
        StaticProperty => -- "the prop (specified in obj)"
            np2inst (DefOneNP (parenthCN 
            (prop2cn prop) (ap2s (ComplAdj specifiedInAdj2 rec))));
        AssocProperty => -- "the set of prop associated with obj"
            np2inst (appFun1 (funGen setN) (IndefManyNP 
            (ModAdj (ComplAdj associatedWithAdj2 (inst2np rec)) (prop2cn prop))))
    };
   
    implPropCallO : Inst -> PropertyL -> Inst = \rec, prop -> case prop.pt of {
        AssocProperty => -- "the set of prop"
            np2inst (appFun1 (funGen setN) (IndefManyNP (prop2cn prop)));
        _ => -- "the prop"
            np2inst (DefOneNP (prop2cn prop))
    };


    mkSimpleProperty : CN -> PropertyL = cn2prop SimpleProperty;
    mkOnProperty : CN -> PropertyL = cn2prop OnProperty;
    mkStaticProperty : CN -> PropertyL = cn2prop StaticProperty;
    mkAssocProperty : CN -> PropertyL = cn2prop AssocProperty;

--
-- Predicates
--

param PredType = VerbGroup | Literal | AlwaysImplicitSent;

lintype PredicateL = 
    VG **  -- a verb group is used for simple properties where the receiver is the subject
    {
        s5 : Str;  -- literal, for "the property blabla(bla, bla) holds for x"
        s6 : Polarity => SBranch;  -- always a sentence (with receiver implicit)
                               -- useful for global state flags e.g. "the correct PIN has been entered"
        pt : PredType 
    };


oper 
    dummySBranch : SBranch = \\_ => "";
    vg2pred : VG -> PredicateL = \vg -> vg ** 
        {s5 = ""; s6 = \\_=> dummySBranch; hasImplicit = False; pt = VerbGroup};
        
    mkIsPredicate : AP -> PredicateL = \ap -> vg2pred (PredAP ap);
    
    mkStrPredicate : Str -> PredicateL = \str -> let 
            dummyVGGer : VG = {s = \\_ => ""; s2 = ""; s3 = \\_ => \\_ => ""; s4 = ""; lock_VG = <>}
        in 
            dummyVGGer ** {
                s5 = str;
                s6 = \\_ => dummySBranch;
                pt = Literal   
            };

    -- FIXME: the 'Literal' case here and in implPredCallO
    predCallO : Inst -> PredicateL -> AS = \rec,pred -> let np = inst2np rec in {
        s = case pred.pt of {
            VerbGroup => table {
                AtomGer.Pos => (PredVP np (PosVG pred)).s;
                AtomGer.Neg => (PredVP np (NegVG pred)).s
            };
            Literal => -- use other declension than nTisch ?
                (mkPred (instFunAn (nTisch pred.s5) rec) (PredAP trueAP)).s;
            AlwaysImplicitSent => pred.s6
       };
       lock_AS = <>
    };
    
    implPredCallO : Inst -> PredicateL -> AS = \rec,pred -> 
        case pred.pt of {
            VerbGroup => -- no implicit form
                predCallO rec pred;
            Literal => mkPred (DefOneNP (UseN (nTisch pred.s5))) (PredAP trueAP);
            AlwaysImplicitSent => {s = pred.s6; lock_AS = <>}
        };
        
       

}

