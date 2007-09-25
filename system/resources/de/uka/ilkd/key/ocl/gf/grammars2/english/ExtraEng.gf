--# -path=.:../prelude:../resourceAbstract:../resourceEnglish

-- Some supplementary resource functions for English.
resource ExtraEng = ResourceEng ** open ParadigmsEng, Prelude, SyntaxEng in {

-- NP  ::= NP Adv
-- NP  ::= NP "as" CN
-- Adv ::= AP

-- NP in capital/small letters (somehow a locative?)
-- NP fom Index a to Index b (somehow a locative?)
-- NP as CN (Congruence)

-- NP appended at the end of NP
-- NP regarded as NP
-- NP rounded

oper

    nounSubjSentence : CN -> Subj -> S -> CN = \cn, subj,x -> 
    {s = \\n,c => cn.s ! n ! c ++ subj.s ++ x.s ; 
     g = cn.g;
     lock_CN = <>
    } ;
                        
                    
-- $NP ::= NP "as" CN$ ("I am in Göteborg as a big city").

  npAlsNP : NP -> CN -> NP = 
    \paris, stadt ->
    {s = \\c => paris.s ! c ++ "as" ++ stadt.s ! paris.n ! (toCase c) ;
     n = paris.n ;
     p = paris.p;
     lock_NP = <>
    } ;

-- NP  ::= NP AdV  ("Paris today")

  advNP : NP -> AdV -> NP = \paris, heute ->
    {s = \\c => paris.s ! c ++ heute.s ;
     n = paris.n ;
     p = paris.p;
     lock_NP = <>
    } ;


-- AdV ::= AP ("gut") (can this be done in English???)

  advAP : AP -> AdV = \gut ->
    {s = gut.s!AAdv;
     p = False;
     lock_AdV = <>
    } ;

-- AdV ::= Subj S ("if it rains") (where does the comma belong?)

  advSubjS : Subj -> S -> AdV = \wenn,esregnet -> {
    s = wenn.s ++ esregnet.s;
    --isPost = True
    p = True;
    lock_AdV = <>
    } ; 

}
