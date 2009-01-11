( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((killed_5 Int Int ) (hates_11 Int Int ) (richer_14 Int Int ) (lives_3 Int ) (type_of_S_1_2 Int ) )
:extrafuns ((butler_6 Int ) (dummy_S_21 Int ) (agatha_4 Int ) (charles_7 Int ) )
:assumption (type_of_S_1_2 butler_6)
:assumption (type_of_S_1_2 dummy_S_21)
:assumption (type_of_S_1_2 agatha_4)
:assumption (type_of_S_1_2 charles_7)
:formula (not (implies true (implies (and (and (and (and (and (and (and (and (and (and (and (and (exists(?z7_0 Int)(and (type_of_S_1_2 ?z7_0) (and (lives_3 ?z7_0) (killed_5 ?z7_0 agatha_4)))) (lives_3 agatha_4)) (lives_3 butler_6)) (lives_3 charles_7)) (forall (?z8_8 Int) (implies (type_of_S_1_2 ?z8_8) (implies (lives_3 ?z8_8) (or (= ?z8_8 agatha_4) (or (= ?z8_8 butler_6) (= ?z8_8 charles_7))))))) (forall (?z9_9 Int) (implies (type_of_S_1_2 ?z9_9) (forall (?z0_10 Int) (implies (type_of_S_1_2 ?z0_10) (implies (killed_5 ?z9_9 ?z0_10) (hates_11 ?z9_9 ?z0_10))))))) (forall (?w1_12 Int) (implies (type_of_S_1_2 ?w1_12) (forall (?w2_13 Int) (implies (type_of_S_1_2 ?w2_13) (implies (killed_5 ?w1_12 ?w2_13) (not (richer_14 ?w1_12 ?w2_13)))))))) (forall (?w3_15 Int) (implies (type_of_S_1_2 ?w3_15) (implies (hates_11 agatha_4 ?w3_15) (not (hates_11 charles_7 ?w3_15)))))) (forall (?w4_16 Int) (implies (type_of_S_1_2 ?w4_16) (implies (not (= ?w4_16 butler_6)) (hates_11 agatha_4 ?w4_16))))) (forall (?w5_17 Int) (implies (type_of_S_1_2 ?w5_17) (implies (not (richer_14 ?w5_17 agatha_4)) (hates_11 butler_6 ?w5_17))))) (forall (?w6_18 Int) (implies (type_of_S_1_2 ?w6_18) (implies (hates_11 agatha_4 ?w6_18) (hates_11 butler_6 ?w6_18))))) (forall (?w7_19 Int) (implies (type_of_S_1_2 ?w7_19) (exists(?w8_20 Int)(and (type_of_S_1_2 ?w8_20) (not (hates_11 ?w7_19 ?w8_20))))))) (not (= agatha_4 butler_6))) (killed_5 agatha_4 agatha_4))))
)