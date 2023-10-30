/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration;

import java.io.File;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class ProofExplorationServiceTest {
    ProofExplorationService expService;
    Proof currentProof;
    File location;
    KeYEnvironment<?> env;

    @BeforeEach
    public void setup() throws ProblemLoaderException {
        location = new File("src/test/resources//org/key_project/exploration/testAdditions.key");
        Assumptions.assumeTrue(location.exists(), "File testAdditions.key not found.");
        env = KeYEnvironment.load(location);
        currentProof = env.getLoadedProof();
        expService = new ProofExplorationService(currentProof, env.getServices());
    }

    // p -> q -> !q -> !p
    @AfterEach
    public void tearDown() {
        env = null;
        expService = null;
        location = null;
        currentProof = null;
    }


    /**
     * Tests that the added term is added correctly and that metadata was added as well
     */
    @Test
    public void testAdditionAntec() {
        Term add = parseTerm("p");
        expService.soundAddition(currentProof.getOpenGoal(currentProof.root()), add, true);
        ImmutableList<Goal> goals = currentProof.openGoals();

        assertEquals(2, goals.size(), "Two new goals created");

        Goal first = goals.head();
        Goal second = goals.tail().head();

        ExplorationNodeData lookup = first.node().lookup(ExplorationNodeData.class);
        assertNotNull(lookup, "First goal is marked as exploration node");

        ExplorationNodeData lookup2 = second.node().lookup(ExplorationNodeData.class);
        assertNotNull(lookup2, "Second goal is marked as exploration node");

        Goal withAddedTerm;
        Goal justification;

        if (!first.node().sequent().antecedent().isEmpty()) {
            withAddedTerm = first;
            justification = second;

        } else {
            withAddedTerm = second;
            justification = first;
        }

        testAddition(withAddedTerm, justification, add, true);
        assertFalse(checkNodeForExplorationDataAndAction(withAddedTerm.node()));
        assertFalse(checkNodeForExplorationDataAndAction(justification.node()));


        assertTrue(checkNodeForExplorationDataAndAction(withAddedTerm.node().parent()),
            "Parent is marked as ExplorationNode and data contains Exploration Action");

        assertFalse(checkNodeForExplorationDataAndAction(withAddedTerm.node()));
        assertFalse(checkNodeForExplorationDataAndAction(justification.node()));

    }

    /**
     * Test tests that the added term is added correctly and that metadata was added as well
     */
    @Test
    public void testAdditionSucc() {
        Term added = parseTerm("q");
        expService.soundAddition(currentProof.getOpenGoal(currentProof.root()), added, false);
        ImmutableList<Goal> goals = currentProof.openGoals();

        assertEquals(2, goals.size(), "Two new goals created");

        Goal first = goals.head();
        Goal second = goals.tail().head();

        ExplorationNodeData lookup = first.node().lookup(ExplorationNodeData.class);
        assertNotNull(lookup, "First goal is marked as exploration node");

        ExplorationNodeData lookup2 = second.node().lookup(ExplorationNodeData.class);
        assertNotNull(lookup2, "Second goal is marked as exploration node");

        Goal withAddedTerm;
        Goal justification;

        if (!first.node().sequent().antecedent().isEmpty()) {
            withAddedTerm = second;
            justification = first;

        } else {
            withAddedTerm = first;
            justification = second;
        }

        testAddition(withAddedTerm, justification, added, false);

        assertTrue(checkNodeForExplorationDataAndAction(withAddedTerm.node().parent()),
            "Parent is marked as ExplorationNode and data contains Exploration Action");

        assertFalse(checkNodeForExplorationDataAndAction(withAddedTerm.node()));
        assertFalse(checkNodeForExplorationDataAndAction(justification.node()));


    }


    // region Change

    /**
     * Test changing the root formula
     */
    @Test
    public void testChangeFormula() {
        Term change = parseTerm("p->p");
        ImmutableList<Goal> goals = currentProof.openGoals();
        assertSame(1, goals.size(), "Prerequisite for test");
        Sequent sequent = goals.head().node().sequent();
        PosInOccurrence pio =
            new PosInOccurrence(sequent.succedent().get(0), PosInTerm.getTopLevel(), false);
        expService.applyChangeFormula(goals.head(), pio, sequent.succedent().get(0).formula(),
            change);
        ImmutableList<Goal> newCreatedGoals = currentProof.openGoals();

        assertEquals(2, newCreatedGoals.size(), "Two new goals created");

        // find hide branch
        Goal applicationBranch = newCreatedGoals.head().isAutomatic() ? newCreatedGoals.head()
                : newCreatedGoals.tail().head();
        Goal justificationBranch = !newCreatedGoals.head().isAutomatic() ? newCreatedGoals.head()
                : newCreatedGoals.tail().head();

        // check meta data
        Node hideNode = applicationBranch.node().parent();

        assertNotNull(hideNode.lookup(ExplorationNodeData.class));
        assertNotNull(justificationBranch.node().lookup(ExplorationNodeData.class));

        assertEquals(new Name("hide_right"), hideNode.getAppliedRuleApp().rule().name(),
            "Hide Right was applied");
        // set all goals to interactive
        justificationBranch.setEnabled(true);
        // perform proof, it has to close
        env.getProofControl().startAndWaitForAutoMode(currentProof, newCreatedGoals);
        assertTrue(currentProof.closed(), "Proof is closed");

    }


    /**
     * Tests that sizes are as expected after addition
     */
    private void testAddition(Goal withAddedTerm, Goal justification, Term added, boolean antec) {
        Semisequent semiSeqAdded =
            antec ? withAddedTerm.sequent().antecedent() : withAddedTerm.sequent().succedent();
        Semisequent parentSemiSeqOfAdded =
            antec ? withAddedTerm.node().parent().sequent().antecedent()
                    : withAddedTerm.node().parent().sequent().succedent();

        Semisequent semiSeqUntouched =
            !antec ? withAddedTerm.sequent().antecedent() : withAddedTerm.sequent().succedent();

        Semisequent parentSemiSeqOfUntouched =
            !antec ? withAddedTerm.node().parent().sequent().antecedent()
                    : withAddedTerm.node().parent().sequent().succedent();


        assertSame(semiSeqAdded.size(), parentSemiSeqOfAdded.size() + 1,
            "The size of the added semisequent has changed");
        assertEquals(semiSeqAdded.get(0).formula(), added, "Added Term is indeed added");
        assertFalse(justification.isAutomatic(), "Justification branch is marked as interactive");

        assertSame(semiSeqUntouched.size(), parentSemiSeqOfUntouched.size(),
            "The size if untouched semisequents is the same");
        assertEquals(semiSeqUntouched, parentSemiSeqOfUntouched,
            "The  untouched semisequents are equal");

        Node parent = withAddedTerm.node().parent();

        assertEquals(parent, justification.node().parent(), "Both nodes have the same parent");
        assertEquals(new Name("cut"), parent.getAppliedRuleApp().rule().name(),
            "The addition was inserted using the cut rule");
    }

    /**
     * Test that exploration metadata have been set to the node
     */
    private boolean checkNodeForExplorationDataAndAction(Node parent) {
        boolean foundExploration = false;
        boolean foundExplorationAction = false;

        ExplorationNodeData lookup = parent.lookup(ExplorationNodeData.class);
        if (lookup != null) {
            foundExploration = true;
            String explorationAction = lookup.getExplorationAction();
            if (explorationAction != null) {
                foundExplorationAction = true;
            }
        }

        return foundExploration & foundExplorationAction;

    }

    private Term parseTerm(String term) {
        KeyIO io = new KeyIO(env.getServices());
        return io.parseExpression(term);
    }
}
