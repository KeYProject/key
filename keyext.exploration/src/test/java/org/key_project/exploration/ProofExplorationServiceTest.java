/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class ProofExplorationServiceTest {
    @Nullable
    ProofExplorationService expService;
    @Nullable
    Proof currentProof;
    @Nullable
    Path location;
    @Nullable
    KeYEnvironment<?> env;

    @BeforeEach
    public void setup() throws ProblemLoaderException {
        Path testLocation =
            Paths.get("src/test/resources//org/key_project/exploration/testAdditions.key");
        Assumptions.assumeTrue(Files.exists(testLocation), "File testAdditions.key not found.");
        KeYEnvironment<?> testEnv = KeYEnvironment.load(testLocation);
        Proof loadedProof = testEnv.getLoadedProof();
        if (loadedProof == null) {
            throw new NullPointerException("No proof loaded from 'testAdditions.key'.");
        }
        location = testLocation;
        env = testEnv;
        currentProof = loadedProof;
        expService = new ProofExplorationService(loadedProof, testEnv.getServices());
    }

    // p -> q -> !q -> !p
    @AfterEach
    public void tearDown() {
        env = null;
        expService = null;
        location = null;
        currentProof = null;
    }

    private Proof requiredProof() {
        if (currentProof == null) {
            throw new NullPointerException("currentProof is null");
        }
        return currentProof;
    }

    private ProofExplorationService requiredExpService() {
        if (expService == null) {
            throw new NullPointerException("expService is null");
        }
        return expService;
    }

    private KeYEnvironment<?> requiredEnv() {
        if (env == null) {
            throw new NullPointerException("env is null");
        }
        return env;
    }

    private Goal openGoalAtRoot() {
        Proof proof = requiredProof();
        Node root = proof.root();
        if (root == null) {
            throw new NullPointerException("The proof has no root node.");
        }
        Goal goal = proof.getOpenGoal(root);
        if (goal == null) {
            throw new NullPointerException("No open goal at the root node.");
        }
        return goal;
    }


    /**
     * Tests that the added term is added correctly and that metadata was added as well
     */
    @Test
    public void testAdditionAntec() {
        JTerm add = parseTerm("p");
        requiredExpService().soundAddition(openGoalAtRoot(), add, true);
        ImmutableList<Goal> goals = requiredProof().openGoals();

        assertEquals(2, goals.size(), "Two new goals created");

        Goal first = goals.head();
        Goal second = goals.tail().head();

        ExplorationNodeData lookup = first.node().lookup(ExplorationNodeData.class);
        if (lookup == null) {
            throw new NullPointerException("First goal is marked as exploration node");
        }
        assertNotNull(lookup, "First goal is marked as exploration node");

        ExplorationNodeData lookup2 = second.node().lookup(ExplorationNodeData.class);
        if (lookup2 == null) {
            throw new NullPointerException("Second goal is marked as exploration node");
        }
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
        JTerm added = parseTerm("q");
        requiredExpService().soundAddition(openGoalAtRoot(), added, false);
        ImmutableList<Goal> goals = requiredProof().openGoals();

        assertEquals(2, goals.size(), "Two new goals created");

        Goal first = goals.head();
        Goal second = goals.tail().head();

        ExplorationNodeData lookup = first.node().lookup(ExplorationNodeData.class);
        if (lookup == null) {
            throw new NullPointerException("First goal is marked as exploration node");
        }
        assertNotNull(lookup, "First goal is marked as exploration node");

        ExplorationNodeData lookup2 = second.node().lookup(ExplorationNodeData.class);
        if (lookup2 == null) {
            throw new NullPointerException("Second goal is marked as exploration node");
        }
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
        JTerm change = parseTerm("p->p");
        ImmutableList<Goal> goals = requiredProof().openGoals();
        assertSame(1, goals.size(), "Prerequisite for test");
        Sequent sequent = goals.head().node().sequent();
        PosInOccurrence pio =
            new PosInOccurrence(sequent.succedent().get(0), PosInTerm.getTopLevel(), false);
        requiredExpService().applyChangeFormula(goals.head(), pio,
            (JTerm) sequent.succedent().get(0).formula(),
            change);
        ImmutableList<Goal> newCreatedGoals = requiredProof().openGoals();

        assertEquals(2, newCreatedGoals.size(), "Two new goals created");

        // find hide branch
        Goal applicationBranch = newCreatedGoals.head().isAutomatic() ? newCreatedGoals.head()
                : newCreatedGoals.tail().head();
        Goal justificationBranch = !newCreatedGoals.head().isAutomatic() ? newCreatedGoals.head()
                : newCreatedGoals.tail().head();

        // check meta data
        Node hideNode = applicationBranch.node().parent();
        if (hideNode == null) {
            throw new NullPointerException("No parent node of the application branch.");
        }

        ExplorationNodeData hideData = hideNode.lookup(ExplorationNodeData.class);
        if (hideData == null) {
            throw new NullPointerException("No exploration data on the application branch.");
        }
        assertNotNull(hideData);

        ExplorationNodeData justificationData =
            justificationBranch.node().lookup(ExplorationNodeData.class);
        if (justificationData == null) {
            throw new NullPointerException("No exploration data on the justification branch.");
        }
        assertNotNull(justificationData);

        RuleApp hideRuleApp = hideNode.getAppliedRuleApp();
        if (hideRuleApp == null) {
            throw new NullPointerException("No applied rule app on the hide node.");
        }
        assertEquals(new Name("hide_right"), hideRuleApp.rule().name(),
            "Hide Right was applied");
        // set all goals to interactive
        justificationBranch.setEnabled(true);
        // perform proof, it has to close
        ProofControl proofControl = requiredEnv().getProofControl();
        if (proofControl == null) {
            throw new NullPointerException("No proof control available.");
        }
        proofControl.startAndWaitForAutoMode(requiredProof(), newCreatedGoals);
        assertTrue(requiredProof().closed(), "Proof is closed");

    }


    /**
     * Tests that sizes are as expected after addition
     */
    private void testAddition(Goal withAddedTerm, Goal justification, JTerm added, boolean antec) {
        Node parent = withAddedTerm.node().parent();
        if (parent == null) {
            throw new NullPointerException("No parent node of the added-term node.");
        }

        Semisequent semiSeqAdded =
            antec ? withAddedTerm.sequent().antecedent() : withAddedTerm.sequent().succedent();
        Semisequent parentSemiSeqOfAdded =
            antec ? parent.sequent().antecedent() : parent.sequent().succedent();

        Semisequent semiSeqUntouched =
            !antec ? withAddedTerm.sequent().antecedent() : withAddedTerm.sequent().succedent();

        Semisequent parentSemiSeqOfUntouched =
            !antec ? parent.sequent().antecedent() : parent.sequent().succedent();


        assertSame(semiSeqAdded.size(), parentSemiSeqOfAdded.size() + 1,
            "The size of the added semisequent has changed");
        assertEquals(semiSeqAdded.get(0).formula(), added, "Added Term is indeed added");
        assertFalse(justification.isAutomatic(), "Justification branch is marked as interactive");

        assertSame(semiSeqUntouched.size(), parentSemiSeqOfUntouched.size(),
            "The size if untouched semisequents is the same");
        assertEquals(semiSeqUntouched, parentSemiSeqOfUntouched,
            "The  untouched semisequents are equal");

        assertEquals(parent, justification.node().parent(), "Both nodes have the same parent");
        RuleApp cutRuleApp = parent.getAppliedRuleApp();
        if (cutRuleApp == null) {
            throw new NullPointerException("No applied rule app on the parent node.");
        }
        assertEquals(new Name("cut"), cutRuleApp.rule().name(),
            "The addition was inserted using the cut rule");
    }

    /**
     * Test that exploration metadata have been set to the node
     */
    private boolean checkNodeForExplorationDataAndAction(@Nullable Node parent) {
        if (parent == null) {
            throw new NullPointerException("The parent node is null.");
        }
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

    private JTerm parseTerm(String term) {
        KeyIO io = new KeyIO(requiredEnv().getServices());
        return io.parseExpression(term);
    }
}
