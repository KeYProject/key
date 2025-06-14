/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.rulefilter.IHTacletFilter;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;


public class TestTacletIndex {

    NoPosTacletApp ruleRewriteNonH1H2;
    NoPosTacletApp ruleNoFindNonH1H2H3;
    NoPosTacletApp ruleAntecH1;
    NoPosTacletApp ruleSucc;
    NoPosTacletApp ruleMisMatch;
    NoPosTacletApp notfreeconflict;

    RuleSet h1;
    RuleSet h2;
    RuleSet h3;

    TacletIndex variante_one;


    private Taclet taclet(String name) {
        return TacletForTests.getTaclet(name).taclet();
    }

    @BeforeEach
    public void setUp() {
        Path tacletFile = HelperClassForTests.TESTCASE_DIRECTORY.resolve(
            "../de/uka/ilkd/key/proof/ruleForTestTacletIndex.taclet");
        assertTrue(Files.exists(tacletFile), "File '" + tacletFile + "' does not exist.");
        TacletForTests.parse(tacletFile);

        h1 = TacletForTests.getHeuristics().lookup(new Name("h1"));
        h2 = TacletForTests.getHeuristics().lookup(new Name("h2"));
        h3 = TacletForTests.getHeuristics().lookup(new Name("h3"));

        ruleRewriteNonH1H2 =
            NoPosTacletApp.createNoPosTacletApp(taclet("rewrite_noninteractive_h1_h2"));
        ruleNoFindNonH1H2H3 =
            NoPosTacletApp.createNoPosTacletApp(taclet("nofind_noninteractive_h1_h2_h3"));
        ruleAntecH1 = NoPosTacletApp.createNoPosTacletApp(taclet("rule_antec_h1"));
        ruleSucc = NoPosTacletApp.createNoPosTacletApp(taclet("rule_succ"));
        ruleMisMatch = NoPosTacletApp.createNoPosTacletApp(taclet("antec_mismatch"));
        notfreeconflict = NoPosTacletApp.createNoPosTacletApp(taclet("not_free_conflict"));


        variante_one = TacletIndexKit.getKit().createTacletIndex();
        variante_one.add(ruleRewriteNonH1H2);
        variante_one.add(ruleNoFindNonH1H2H3);
        variante_one.add(ruleAntecH1);
        variante_one.add(ruleSucc);


    }


    @AfterEach
    public void tearDown() {
        ruleRewriteNonH1H2 = null;
        ruleNoFindNonH1H2H3 = null;
        ruleAntecH1 = null;
        ruleSucc = null;
        ruleMisMatch = null;
        notfreeconflict = null;

        h1 = null;
        h2 = null;
        h3 = null;

        variante_one = null;
    }


    private boolean isRuleIn(ImmutableList<? extends TacletApp> l, TacletApp rule) {
        for (TacletApp aL : l) {
            if (aL.taclet() == rule.taclet()) {
                return true;
            }
        }
        return false;
    }


    /**
     * test disabled. Since 0.632 "noninteractive" is disabled
     */
    @Test
    @Disabled
    public void disabled_testNonInteractiveIsShownOnlyIfHeuristicIsMissed() {
        JTerm term_p1 = TacletForTests.parseTerm("p(one, zero)");
        ImmutableList<RuleSet> listofHeuristic = ImmutableSLList.nil();
        listofHeuristic = listofHeuristic.prepend(h3);
        PosInOccurrence pos =
            new PosInOccurrence(new SequentFormula(term_p1), PosInTerm.getTopLevel(), true);
        assertTrue(
            isRuleIn(variante_one.getAntecedentTaclet(pos,
                new IHTacletFilter(true, listofHeuristic), null), ruleRewriteNonH1H2),
            "Noninteractive antecrule is not in list, but none of its" + "heuristics is active.");

        assertFalse(
            isRuleIn(
                variante_one.getAntecedentTaclet(pos,
                    new IHTacletFilter(true, listofHeuristic.prepend(h1)), null),
                ruleRewriteNonH1H2),
            "Noninteractive antecrule is in list, but one of its " + "heuristics is active.");

        assertTrue(
            isRuleIn(
                variante_one.getNoFindTaclet(new IHTacletFilter(true, ImmutableSLList.nil()), null),
                ruleNoFindNonH1H2H3),
            "Noninteractive nofindrule is not in list, but none of its " + "heuristics is active.");

        assertFalse(
            isRuleIn(variante_one.getNoFindTaclet(new IHTacletFilter(true, listofHeuristic), null),
                ruleNoFindNonH1H2H3),
            "Noninteractive nofindrule is in list, but one of its " + "heuristics is active.");

    }


    @Test
    public void testShownIfHeuristicFits() {
        Services services = new Services(AbstractProfile.getDefaultProfile());
        ImmutableList<RuleSet> listofHeuristic = ImmutableSLList.nil();
        listofHeuristic = listofHeuristic.prepend(h3).prepend(h2);

        JTerm term_p1 = TacletForTests.parseTerm("p(one, zero)");

        SequentFormula cfma = new SequentFormula(term_p1);

        PosInOccurrence posSucc =
            new PosInOccurrence(cfma, PosInTerm.getTopLevel(), false);

        assertTrue(
            isRuleIn(variante_one.getSuccedentTaclet(posSucc,
                new IHTacletFilter(true, listofHeuristic), services), ruleSucc),
            "ruleSucc has no heuristics, but is not in succ list.");

        assertFalse(
            isRuleIn(variante_one.getRewriteTaclet(posSucc,
                new IHTacletFilter(true, listofHeuristic), services), ruleSucc),
            "ruleSucc has no heuristics, but is in rewrite list.");


        assertFalse(
            isRuleIn(variante_one.getSuccedentTaclet(posSucc,
                new IHTacletFilter(false, listofHeuristic), services), ruleSucc),
            "ruleSucc has no heuristics, but is" + " in heuristic succ list.");

        assertFalse(isRuleIn(
            variante_one.getNoFindTaclet(new IHTacletFilter(false, listofHeuristic), services),
            ruleSucc), "ruleSucc has no heuristics, but is" + " in heuristic of nofind list.");
    }

    @Test
    public void testNoMatchingFindRule() {
        Services services = new Services(AbstractProfile.getDefaultProfile());
        ImmutableList<RuleSet> listofHeuristic = ImmutableSLList.nil();

        JTerm term_p2 = TacletForTests.parseTerm("\\forall nat z; p(z, one)").sub(0);

        PosInOccurrence posAntec =
            new PosInOccurrence(new SequentFormula(term_p2), PosInTerm.getTopLevel(), true);
        PosInOccurrence posSucc =
            new PosInOccurrence(new SequentFormula(term_p2), PosInTerm.getTopLevel(), true);


        assertFalse(
            isRuleIn(variante_one.getAntecedentTaclet(posAntec,
                new IHTacletFilter(true, listofHeuristic), services), ruleRewriteNonH1H2),
            "rule matched, but no match possible");


        listofHeuristic = listofHeuristic.prepend(h3).prepend(h2).prepend(h1);

        assertFalse(
            isRuleIn(variante_one.getSuccedentTaclet(posSucc,
                new IHTacletFilter(true, listofHeuristic), services), ruleSucc),
            "ruleSucc matched but matching not possible");
    }

    @Test
    public void testMatchConflictOccurs() {
        Services services = new Services(AbstractProfile.getDefaultProfile());
        TacletIndex ruleIdx = TacletIndexKit.getKit().createTacletIndex();
        ruleIdx.add(ruleRewriteNonH1H2);
        ruleIdx.add(ruleNoFindNonH1H2H3);
        ruleIdx.add(ruleAntecH1);
        ruleIdx.add(ruleSucc);
        ruleIdx.add(ruleMisMatch);

        JTerm term_p4 = TacletForTests.parseTerm("p(zero, one)");

        ImmutableList<RuleSet> listofHeuristic = ImmutableSLList.nil();
        PosInOccurrence posAntec =
            new PosInOccurrence(new SequentFormula(term_p4), PosInTerm.getTopLevel(), true);

        assertFalse(
            isRuleIn(ruleIdx.getAntecedentTaclet(posAntec,
                new IHTacletFilter(true, listofHeuristic), services), ruleMisMatch),
            "rule matched, but no match possible");

    }

    @Test
    public void testNotFreeInYConflict() {
        TacletIndex ruleIdx = TacletIndexKit.getKit().createTacletIndex();
        ruleIdx.add(notfreeconflict);

        JTerm term_p5 = TacletForTests.parseTerm("\\forall nat z; p(f(z), z)");
        SequentFormula cfma_p5 = new SequentFormula(term_p5);
        Sequent seq_p5 = JavaDLSequentKit.createAnteSequent(
            ImmutableSLList.singleton(cfma_p5));
        PosInOccurrence pio_p5 =
            new PosInOccurrence(cfma_p5, PosInTerm.getTopLevel(), true);
        RuleAppIndex appIdx = createGoalFor(seq_p5, ruleIdx);

        assertFalse(
            isRuleIn(appIdx.getTacletAppAt(TacletFilter.TRUE, pio_p5, null), notfreeconflict),
            "No rule should match");

        JTerm term_p6 = TacletForTests.parseTerm("\\forall nat z; p(zero, z)");

        SequentFormula cfma_p6 = new SequentFormula(term_p6);
        Sequent seq_p6 = JavaDLSequentKit.createAnteSequent(
            ImmutableSLList.singleton(cfma_p6));
        PosInOccurrence pio_p6 =
            new PosInOccurrence(cfma_p6, PosInTerm.getTopLevel(), true);
        appIdx = createGoalFor(seq_p6, ruleIdx);

        assertTrue(
            isRuleIn(appIdx.getTacletAppAt(TacletFilter.TRUE, pio_p6, null), notfreeconflict),
            "One rule should match");

    }

    private RuleAppIndex createGoalFor(Sequent seq_p5, TacletIndex ruleIdx) {
        final Node node_p5 = new Node(new Proof("TestTacletIndex",
            new InitConfig(new Services(AbstractProfile.getDefaultProfile()))), seq_p5);
        final BuiltInRuleAppIndex builtinIdx = new BuiltInRuleAppIndex(new BuiltInRuleIndex());
        final Goal goal_p5 =
            new Goal(node_p5, ruleIdx, builtinIdx, node_p5.proof().getServices());
        return goal_p5.ruleAppIndex();
    }


}
