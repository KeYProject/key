/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.lang.reflect.Method;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * class tests the goal, especially the split and set back mechanism.
 */

public class TestGoal {

    private Proof proof;

    @BeforeEach
    public void setUp() {
        TacletForTests.parse();
        proof = new Proof("", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
    }

    @AfterEach
    public void tearDown() {
        proof.dispose();
        proof = null;
    }

    @Test
    public void testSetBack0() {
        Sequent seq = JavaDLSequentKit.createSuccSequent(
            ImmutableList.singleton(new SequentFormula(TacletForTests.parseTerm("A"))));

        final InitConfig initConfig =
            new InitConfig(new Services(AbstractProfile.getDefaultProfile()));
        proof = new Proof("", seq, null, initConfig.createTacletIndex(),
            initConfig.createBuiltInRuleIndex(), initConfig);


        Goal g = proof.openGoals().head();// new Goal(proof.root(), new RuleAppIndex(new
                                          // TacletAppIndex(new TacletIndex(), proof.getServices()),
                                          // new BuiltInRuleAppIndex(new BuiltInRuleIndex()),
                                          // proof.getServices()));
        ImmutableList<Goal> lg = g.split(3);
        lg.head().addNoPosTacletApp(TacletForTests.lookupTaclet("imp_right"));
        lg.tail().head().addNoPosTacletApp(TacletForTests.lookupTaclet("imp_left"));
        lg.tail().tail().head().addNoPosTacletApp(TacletForTests.lookupTaclet("or_right"));
        // just check if the test is trivially correct because of rules
        // not found
        assertNotNull(lg.head().indexOfTaclets().lookup("imp_right"));

        ImmutableList<Goal> lg0 = lg.head().split(3);
        ImmutableList<Goal> lg00 = lg0.tail().head().split(8);
        ImmutableList<Goal> lg1 = lg.tail().tail().head().split(2);
        proof.add(lg1.append(lg00).append(lg0.head()).append(lg0.tail().tail().head())
                .append(lg.tail().head()));
        proof.pruneProof(lg.tail().head());
        assertEquals(1, proof.openGoals().size());
        assertNull(proof.openGoals().head().indexOfTaclets().lookup("imp_right"),
            "Taclet Index of set back goal contains rule \"imp-right\" that were not "
                + "there before");
        assertNull(proof.openGoals().head().indexOfTaclets().lookup("or_right"),
            "Taclet Index of set back goal contains rule \"or-right\"that were not "
                + "there before");
        assertNull(proof.openGoals().head().indexOfTaclets().lookup("imp_left"),
            "Taclet Index of set back goal contains rule \"imp-left\" that were not "
                + "there before");

    }

    /**
     * Regression test for the pruning bug where taclets introduced (e.g. via {@code \addrules}) at
     * the leaf of a branch other than the one the pruning descends first ("firstLeaf") kept their
     * justification registered in the {@link InitConfig}. On the next automatic run a fresh taclet
     * with the same name would then be registered, causing
     * "A rule named ... has already been registered."
     * <p>
     * The locally introduced taclets are stored on the node at which they were introduced, so the
     * deregistration during pruning must iterate the node itself, not its parent.
     */
    @Test
    public void testSetBackRemovesJustificationOfResidualBranch() {
        Sequent seq = JavaDLSequentKit.createSuccSequent(
            ImmutableList.of(new SequentFormula(TacletForTests.parseTerm("A"))));
        final InitConfig initConfig =
            new InitConfig(new Services(AbstractProfile.getDefaultProfile()));
        proof = new Proof("", seq, null, initConfig.createTacletIndex(),
            initConfig.createBuiltInRuleIndex(), initConfig);

        Goal g = proof.openGoals().head();
        ImmutableList<Goal> lg = g.split(2);
        // split() reuses 'this' (g) for the first child node and clones for the rest, prepending
        // the clones to the result list. Hence lg.head() is attached to the second child (a
        // residual leaf during pruning) and lg.tail().head() is g, attached to the first child
        // (firstLeaf).
        final Goal residualGoal = lg.head();
        final Goal firstGoal = lg.tail().head();
        proof.add(residualGoal);

        final var onFirst = TacletForTests.lookupTaclet("imp_right").taclet();
        final var onResidual = TacletForTests.lookupTaclet("or_left").taclet();
        firstGoal.addTaclet(onFirst, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        residualGoal.addTaclet(onResidual, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);

        assertNotNull(initConfig.getJustifInfo().getJustification(onFirst));
        assertNotNull(initConfig.getJustifInfo().getJustification(onResidual));

        proof.pruneProof(proof.root());

        assertNull(initConfig.getJustifInfo().getJustification(onFirst),
            "justification of taclet introduced on the firstLeaf branch must be removed on prune");
        assertNull(initConfig.getJustifInfo().getJustification(onResidual),
            "justification of taclet introduced on a residual branch leaf must be removed on prune");
    }

    @Test
    public void testSetBack1() throws Exception {
        Sequent seq = JavaDLSequentKit.createSuccSequent(
            ImmutableList.singleton(new SequentFormula(TacletForTests.parseTerm("A"))));
        Node root = new Node(proof, seq);
        proof.setRoot(root);
        Goal g = new Goal(root, TacletIndexKit.getKit().createTacletIndex(),
            new BuiltInRuleAppIndex(new BuiltInRuleIndex()), proof.getServices());
        ImmutableList<Goal> lg = g.split(3);
        lg.head().addNoPosTacletApp(TacletForTests.lookupTaclet("imp_right"));
        lg.tail().head().addNoPosTacletApp(TacletForTests.lookupTaclet("imp_left"));
        lg.tail().tail().head().addNoPosTacletApp(TacletForTests.lookupTaclet("or_right"));
        // just check if the test is trivially correct because of rules
        // not found
        assertNotNull(lg.head().indexOfTaclets().lookup("imp_right"));

        ImmutableList<Goal> lg0 = lg.head().split(4);
        lg0.head().addNoPosTacletApp(TacletForTests.lookupTaclet("or_left"));
        lg0.tail().head().addNoPosTacletApp(TacletForTests.lookupTaclet("or_left"));
        ImmutableList<Goal> lg1 = lg.tail().tail().head().split(2);
        proof.add(lg1.append(lg0).append(lg.tail().head()));
        proof.pruneProof(lg0.tail().head());

        assertEquals(4, proof.openGoals().size());

        assertTrue(proof.openGoals().contains(lg1.head()));
        assertNotNull(lg1.head().indexOfTaclets().lookup("or_right"));
        //

        // use reflection as method has private access
        Method remove = proof.getClass().getDeclaredMethod("remove", Goal.class);
        remove.setAccessible(true);

        assertNull(lg1.head().indexOfTaclets().lookup("or_left"));
        remove.invoke(proof, lg1.head());


        assertTrue(proof.openGoals().contains(lg1.tail().head()));
        assertNotNull(lg1.tail().head().indexOfTaclets().lookup("or_right"));
        //
        assertNull(lg1.tail().head().indexOfTaclets().lookup("or_left"));
        // use reflection as method has private access
        remove.invoke(proof, lg1.tail().head());

        if (proof.openGoals().head().indexOfTaclets().lookup("imp_right") != null) {
            assertNotNull(proof.openGoals().tail().head().indexOfTaclets().lookup("imp_left"));
        } else {
            assertNull(proof.openGoals().head().indexOfTaclets().lookup("imp_left"));
            assertNull(proof.openGoals().tail().head().indexOfTaclets().lookup("imp_right"));
        }
        assertNull(proof.openGoals().head().indexOfTaclets().lookup("or_left"));
        assertNull(proof.openGoals().tail().head().indexOfTaclets().lookup("or_left"));

    }

}
