--# -path=.:../prelude:../resourceAbstract:../resourceEnglish

resource PropsAndPredsEng = open Prelude, TypesEng, ResourceEng, 
    ParadigmsEng, PredicationEng, AtomEng, MorphoEng,
    myTypesEng, internalOperEng, myResourceExtEng in { -- 


--
-- Properties
--
param PropType = SimpleProperty | OnProperty  | StaticProperty | AssocProperty;

lintype
    PropertyL  = { -- {s:CN; pt : PropType}
        s : Number => Case => Str;
        g : Gender;
        pt : PropType
    };
oper 
    prop2cn : PropertyL -> CN = \p -> {s=p.s; g=p.g; lock_CN=<>};
    cn2prop : PropType -> CN -> PropertyL = \pt,cn -> {s=cn.s; g=cn.g; pt = pt};
    
    propCallO : Inst -> PropertyL -> Inst = \rec, prop -> case prop.pt of {
        SimpleProperty => -- "the prop of the obj"
            np2inst (appFun1 (funOfCN (prop2cn prop)) rec);
        OnProperty => -- "the prop on obj"
            instFunOnCN (prop2cn prop) rec;
        StaticProperty => -- "the prop (specified in obj)"
            np2inst (DefOneNP (parenthCN 
            (prop2cn prop) (ap2s (ComplAdj specifiedInAdj2 rec))));
        AssocProperty => -- "the set of prop associated with obj"
            np2inst (appFun1 (funNonhuman "set") (IndefManyNP 
            (ModAdj (ComplAdj associatedWithAdj2 (inst2np rec)) (prop2cn prop))))
    };
    
    implPropCallO : Inst -> PropertyL -> Inst = \rec, prop -> case prop.pt of {
        AssocProperty => -- "the set of prop"
            np2inst (appFun1 (funNonhuman "set") (IndefManyNP (prop2cn prop)));
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
        s3 : Str;  -- literal, for "the property blabla(bla, bla) holds for x"
        s4 : Polarity => SBranch;  -- always a sentence (with receiver implicit)
                               -- useful for global state flags e.g. "the correct PIN has been entered"
        pt : PredType 
    };


oper vg2pred : VG -> PredicateL = \vg -> vg ** 
        {s3 = ""; s4 = table {_ => ""}; hasImplicit = False; pt = VerbGroup};
        
    mkIsPredicate : AP -> PredicateL = \ap -> vg2pred (PredAP ap);
    
    mkStrPredicate : Str -> PredicateL = \str -> let 
            dummyVGEng : VG = {s = \\_ => \\_ => ""; s2 = \\_ => \\_ => ""; isAuxT = False; isAuxF = False; lock_VG = <>}
        in 
            dummyVGEng ** {
                s3 = str;
                s4 = table {_ => ""};
                pt = Literal   
            };
    
    predCallO : Inst -> PredicateL -> AS = \rec,pred -> let np = inst2np rec in {
        s = case pred.pt of {
            VerbGroup => table {
                AtomEng.Pos => (PredVP np (PosVG pred)).s;
                AtomEng.Neg => (PredVP np (NegVG pred)).s
            };
            Literal => table { -- TODO: use resource constructions here:
                AtomEng.Pos => ["the property"] ++ pred.s3 ++ ["holds for"] ++ inst2str rec;
                AtomEng.Neg => ["the property"] ++ pred.s3 ++ ["does not hold for"] ++ inst2str rec
            };
            AlwaysImplicitSent => pred.s4
        };
        lock_AS = <>
     };
     
    implPredCallO : Inst -> PredicateL -> AS = \rec,pred -> 
        case pred.pt of {
            VerbGroup => -- no implicit form
                 predCallO rec pred;
            Literal => {s = table { -- TODO: use resource constructions here:
                AtomEng.Pos => ["the property"] ++ pred.s3 ++ ["holds"];
                AtomEng.Neg => ["the property"] ++ pred.s3 ++ ["does not hold"]
                }
            };
            AlwaysImplicitSent => {s = pred.s4}
        };

    
}

{-
-- low-level representation of predicates: a predicate is a function from
-- Inst to Sent. We cannot have functions Inst -> Sent in a lintype. 
-- If we restrict ourselves to just one occurence of the Inst 
-- in the Sent, we can represent this by two parts of the sentence: one which
-- goes before the Inst, one which goes after.
-- in English resource grammar, we inflect atomsents with polarity,
-- but not e.g. word order
lintype
    PredicateL = {
        s0 : Number => Person => Polarity => Str;  -- comes before the argument to the pred
        s1 : Number => Person => Polarity => Str; -- comes after the argument to the pred
        s2 : Number => Person => Polarity => Str; -- implicit version (without mentioning arg)
        npf : NPForm; -- how to inflect the argument (Inst/NP)
        hasImplicit : Bool -- is the s2 field meaningful for this predicate?
    }; 

    predCallO : Inst -> PredicateL -> AS = \rec,pred -> let np = inst2np rec in {
        s = \\pol => pred.s0!np.n!np.p!pol ++ np.s!pred.npf ++ pred.s1!np.n!np.p!pol;
        lock_AS = <>
    };
    
    implPredCallO : Inst -> PredicateL -> AS = \rec,pred -> let np = inst2np rec in {
        s = \\pol => case pred.hasImplicit of {
            True =>  pred.s2!np.n!np.p!pol;
            False => pred.s0!np.n!np.p!pol ++ np.s!pred.npf ++ pred.s1!np.n!np.p!pol
        };
        lock_AS = <>
    };
    
    mkIsProperty : AP -> PredicateL = \ap -> {
        s0 = \\_,_,_ =>  ""; 
        s1 = \\_,p => table {
            AtomEng.Pos => verbBe.s ! (Indic p) ++ ap.s ! AAdj;
            AtomEng.Neg => verbBe.s ! (Indic p) ++ "not" ++ ap.s ! AAdj
        };
        s2 = \\_,_,_ => "";
        npf = NomP;
        hasImplicit = False
    };

    mkBooleanProperty : CN -> PredicateL = \cn -> { 
        -- the CN should really be just a Str
        -- keep it for backwards compatibility until gramm.gen + jcapi is changed
        s0 = \\_,_,_ => ["the property"] ++ cn.s ! Sg ! Nom ++ ["on"];
        s1 = \\_,_,pol => "is" ++ case pol of {
            AtomEng.Pos => "true";
            AtomEng.Neg => ["not true"]
        };
        s2 = \\_,_,pol => ["the property"] ++ cn.s ! Sg ! Nom ++ "is" ++ case pol of {
            AtomEng.Pos => "true";
            AtomEng.Neg => ["not true"]
        };
        npf = NomP; -- ?
        hasImplicit = True
    };

};
-}