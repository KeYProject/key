--# -path=.:../resourceAbstract:../prelude:../resourceGerman

-- Some supplementary resource functions for German.
resource ExtraGer = ResourceGer ** open Prelude, SyntaxGer in {

-- NP  ::= NP Adv
-- NP  ::= NP "als" CN
-- Adv ::= AP

-- NP in Gross-/Kleinbuchstaben (somehow a locative?)
-- NP von Index a bis Index b (somehow a locative?)
-- NP als CN (Congruence)

-- NP angehngt an das Ende von NP
-- NP betrachtet als NP
-- NP echt gerundet

oper

-- $NP ::= NP "als" CN$ ("Ich bin in Gdt").

  npAlsNP : NP -> CN -> NP =
    \paris, stadt ->
    {s = \\c => paris.s ! c ++ "als" ++ stadt.s ! Strong ! paris.n ! (caseNP c) ;
     n = paris.n ;
     p = paris.p ;
     pro = False;
     lock_NP = <>
    } ;

-- NP  ::= NP AdV  ("Paris heute")

  advNP : NP -> AdV -> NP = \paris, heute ->
    {s = \\c => paris.s ! c ++ heute.s ;
     n = paris.n ;
     p = paris.p ;
     pro = False;
     lock_NP = <>
    } ;

-- AdV ::= AP ("gut")

  advAP : AP -> AdV = \gut ->
    {s = gut.s ! APred;
     lock_AdV = <>
    } ;

-- AdV ::= Subj S ("wenn es regnet") (where does the comma belong?)

  advSubjS : Subj -> S -> AdV = \wenn,esregnet -> {
    s = "," ++ wenn.s ++ esregnet.s ! Sub;
    lock_AdV = <>
    } ;

oper

  nounSubjSentence : CN -> Subj -> S -> CN = \cn, subj,x -> 
    {s = \\a,n,c => cn.s ! a ! n ! c ++ subj.s ++ x.s!Sub ; 
     g = cn.g;
     lock_CN = <>
    } ;


}