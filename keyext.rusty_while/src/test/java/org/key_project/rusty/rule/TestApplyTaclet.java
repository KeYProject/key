/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.TacletIndex;
import org.key_project.rusty.util.TacletForTests;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class TestApplyTaclet {
    final static String[] strings = {
        "", "(A -> B) -> (!(!(A -> B)))"
    };
    Proof[] proof;


    private static Semisequent parseTermForSemisequent(String t) {
        if ("".equals(t)) {
            return Semisequent.EMPTY_SEMISEQUENT;
        }
        SequentFormula cf0 = new SequentFormula(TacletForTests.parseTerm(t));
        return Semisequent.EMPTY_SEMISEQUENT.insert(0, cf0).semisequent();
    }

    private Goal createGoal(Node n, TacletIndex tacletIndex) {
        // final BuiltInRuleAppIndex birIndex = new BuiltInRuleAppIndex(new BuiltInRuleIndex());
        return new Goal(n, tacletIndex, n.proof().getServices());
    }

    @BeforeEach
    public void setUp() {
        TacletForTests.setStandardFile(TacletForTests.testRules);
        TacletForTests.parse();
        assert TacletForTests.services().getNamespaces().programVariables()
                .lookup(new Name("i")) != null;

        proof = new Proof[strings.length / 2];

        for (int i = 0; i < proof.length; i++) {
            Semisequent antec = parseTermForSemisequent(strings[2 * i]);
            Semisequent succ = parseTermForSemisequent(strings[2 * i + 1]);
            Sequent s = Sequent.createSequent(antec, succ);
            proof[i] = new Proof("TestApplyTaclet", TacletForTests.initConfig());
            proof[i].setRoot(new Node(proof[i], s));
        }
    }

    @Test
    public void testSuccTacletWithoutIf() {
        Term fma = proof[0].root().sequent().succedent().getFirst().formula();
        NoPosTacletApp impright = TacletForTests.getRules().lookup(new Name("imp_right"));
        TacletIndex tacletIndex = new TacletIndex();
        tacletIndex.add(impright);
        Goal goal = createGoal(proof[0].root(), tacletIndex);
        PosInOccurrence applyPos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(applyPos, null);
        assertEquals(1, rApplist.size(), "Too many or zero rule applications.");
        RuleApp rApp = rApplist.head();
        assertTrue(rApp.complete(), "Rule App should be complete");
        ImmutableList<Goal> goals = rApp.execute(goal, TacletForTests.services());
        assertEquals(1, goals.size(), "Too many or zero goals for imp-right.");
        Sequent seq = goals.head().sequent();
        assertEquals(seq.antecedent().getFirst().formula(), fma.sub(0),
            "Wrong antecedent after imp-right");
        assertEquals(seq.succedent().getFirst().formula(), fma.sub(1),
            "Wrong succedent after imp-right");
    }
}
