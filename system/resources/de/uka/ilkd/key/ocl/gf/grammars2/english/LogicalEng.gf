--# -path=.:../prelude:../resourceAbstract:../resourceEnglish

-- Slightly ad hoc and formal negation and connectives.
resource LogicalEng = ResourceEng ** open  ParadigmsEng, SyntaxEng, ResourceExtEng, myResourceExtEng in {

  oper
    negS : S -> S ;         -- it is not the case, that S
    univS : CN -> S -> S ;  -- for all CNs it holds, that S
    existS : CN -> S -> S ; -- there exists a CN, such that S
    existManyS : CN -> S -> S ; -- there exist CNs, such that S
--.

    negS : S -> S = \A -> 
      PredVP ItNP (NegVG (PredNP (DefOneNP (CNthatS (UseN (nNonhuman "case")) A)))) ;
    univS = \A,B ->
      PredVP ItNP (AdvVP (PosVG (PredVS (v2vs (mkV "hold" "holds" "held" "held")) B))
                    ((prepPhrase "for" (DetNP AllDet A)) ** {lock_AdV = <>})) ;
    existS = \A,B -> ThereNP (IndefOneNP (ModRC A (RelSuch B)));
--      PredVP ItNP (PosTV (tvDir (mkV "give" "gives" "gave" "given"))
--                     (IndefOneNP (ModRC A (RelSuch B)))) ;
    existManyS = \A,B -> ThereNP (IndefManyNP (ModRC A (RelSuch B)));
--     PredVP ItNP (PosTV (tvDir (mkV "give" "gives" "gave" "given"))
--                    (IndefManyNP (ModRC A (RelSuch B)))) ;
} ;
