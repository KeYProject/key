// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.join;

import java.io.File;

import junit.framework.TestCase;

import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionUntilJoinPointMacro;
import de.uka.ilkd.key.macros.FullAutoPilotWithJMLSpecJoinsProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.join.procedures.JoinIfThenElseAntecedent;
import de.uka.ilkd.key.rule.join.procedures.JoinWeaken;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * Test suite for the join rule.
 *
 * @author Dominic Scheurer
 */
public class JoinRuleTests extends TestCase {

    private static final String TEST_RESOURCES_DIR_PREFIX =
            "resources/testcase/join/";

    /**
     * Simple regression test case loading an existing closed proof (standard
     * Gcd example) including two joins with ITE antecedent joins and trying to
     * replay it.
     *
     * @throws ProblemLoaderException
     *             If the proof could not be loaded.
     */
    @Test
    public void testLoadGcdProof() {
        Proof proof = loadProof("gcd.closed.proof");
        assertTrue(proof.closed());
    }

    /**
     * Simple regression test case loading an existing closed proof (standard
     * Gcd example) including two joins with predicate abstraction and trying to
     * replay it.
     *
     * @throws ProblemLoaderException
     *             If the proof could not be loaded.
     */
    @Test
    public void testLoadGcdProofWithPredAbstr() {
        Proof proof = loadProof("gcd.closed.predicateabstraction.proof");
        assertTrue(proof.closed());
    }

    /**
     * Simple regression test case loading an existing closed proof (standard
     * Gcd example) including two joins with predicate abstraction (with lattice
     * elements manually chosen by the user) and trying to replay it.
     *
     * @throws ProblemLoaderException
     *             If the proof could not be loaded.
     */
    @Test
    public void testLoadGcdProofWithPredAbstrAndUserChoices() {
        Proof proof = loadProof("gcd.closed.predicateAbstractionWithUserChoices.proof");
        assertTrue(proof.closed());
    }

    /**
     * Runs the FullAutoPilotWithJMLSpecJoinsProofMacro on the problem with join
     * blocks specified in JML, following by an automatic strategy finish. At
     * the end, there should be two join applications, and the proof should be
     * closed.
     */
    @Test
    public void testDoAutomaticGcdProofWithJoins() {
        final Proof proof = loadProof("gcd.joinBlocks.key");
        runMacro(new FullAutoPilotWithJMLSpecJoinsProofMacro(), proof.root());
        startAutomaticStrategy(proof);

        assertTrue(proof.closed());
        assertEquals("There should be two join applications in the proof.", 2,
                proof.getStatistics().joinRuleApps);
    }

    /**
     * This test case semi-automatically proves the Gcd problem with two joins
     * in the following way:
     * <p>
     * 
     * <ol>
     * <li>Run the {@link FinishSymbolicExecutionUntilJoinPointMacro} on the
     * root</li>
     * <li>Do one join</li>
     * <li>Again run the macro on the one open goal</li>
     * <li>Do another join</li>
     * <li>Let the automatic strategy finish the proof</li>
     * </ol>
     * <p>
     * 
     * At the end, the proof should be closed.
     *
     * @throws ProblemLoaderException
     *             If the proof could not be loaded.
     */
    @Test
    public void testDoManualGcdProof() throws Exception {
        final Proof proof = loadProof("gcd.key");

        for (int i = 0; i < 2; i++) {
            runMacro(new FinishSymbolicExecutionUntilJoinPointMacro(), proof
                    .openGoals().head().node());
            joinFirstGoal(proof, JoinIfThenElseAntecedent.instance());
        }

        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    /**
     * Joins for SE states with different symbolic states are only allowed if
     * the path conditions are distinguishable -- for the case that if-then-else
     * conditions are employed. This test case tries to join two states with
     * equal path condition but different symbolic states -- therefore, the join
     * should fail due to an incomplete rule application.
     */
    @Test
    public void testJoinIndistinguishablePathConditionsWithITE() {
        final Proof proof = loadProof("IndistinguishablePathConditions.proof");

        try {
            joinFirstGoal(proof, JoinIfThenElseAntecedent.instance());
            fail("The join operation should not be applicable.");
        }
        catch (IncompleteRuleAppException e) {
        }
    }

    /**
     * Same as testJoinIndistinguishablePathConditionsWithITE(), but with two
     * join partners.
     */
    @Test
    public void testJoinThreeIndistinguishablePathConditionsWithITE() {
        final Proof proof =
                loadProof("IndistinguishablePathConditions.twoJoins.proof");

        try {
            joinFirstGoal(proof, JoinIfThenElseAntecedent.instance());
            fail("The join operation should not be applicable.");
        }
        catch (IncompleteRuleAppException e) {
        }
    }

    /**
     * Joins two SE states with different symbolic states and equal path
     * condition, but uses the "Full Anonymization" join method for which this
     * is irrelevant. The join should succeed and the proof should be closable.
     */
    @Test
    public void testJoinIndistinguishablePathConditionsWithFullAnonymization() {
        final Proof proof = loadProof("IndistinguishablePathConditions.proof");

        joinFirstGoal(proof, JoinWeaken.instance());
        startAutomaticStrategy(proof);

        assertTrue(proof.closed());
        assertEquals(1, proof.getStatistics().joinRuleApps);
    }

    /**
     * Runs the automatic JavaDL strategy on the given proof.
     *
     * @param proof
     *            Proof to prove automatically.
     */
    private void startAutomaticStrategy(final Proof proof) {
        ProofStarter starter = new ProofStarter(false);
        starter.init(proof);
        starter.start();
    }

    /**
     * Joins the first open goal in the given proof. Asserts that the
     * constructed join rule application is complete.
     *
     * @param proof
     *            The proof the first goal of which to join with suitable
     *            partner(s).
     */
    private void joinFirstGoal(final Proof proof, JoinProcedure joinProc) {
        final Services services = proof.getServices();
        final JoinRule joinRule = JoinRule.INSTANCE;

        final Goal joinGoal = proof.openGoals().head();
        final Node joinNode = joinGoal.node();
        final PosInOccurrence joinPio = getPioFirstFormula(joinNode.sequent());
        final JoinRuleBuiltInRuleApp joinApp =
                (JoinRuleBuiltInRuleApp) joinRule.createApp(joinPio, services);

        {
            joinApp.setJoinPartners(JoinRule.findPotentialJoinPartners(proof
                    .openGoals().head(), joinPio));
            joinApp.setConcreteRule(joinProc);
            joinApp.setJoinNode(joinNode);
        }

        if (!joinApp.complete()) {
            throw new IncompleteRuleAppException();
        }

        joinGoal.apply(joinApp);
    }

    /**
     * @param sequent
     *            Sequent to get the PIO of the first succedent formula for.
     * @return The PIO for the first succedent formula of the given sequent.
     */
    private PosInOccurrence getPioFirstFormula(Sequent sequent) {
        return new PosInOccurrence(sequent.succedent().getFirst(),
                PosInTerm.getTopLevel(), false);
    }

    /**
     * Runs the given macro on the given proof node.
     *
     * @param macro
     *            The macro to execute.
     * @param node
     *            The node to execute the macro on.
     */
    private void runMacro(AbstractProofMacro macro, Node node) {
        try {
            macro.applyTo(null, node, null, null);
        }
        catch (Exception e) {
            fail("Could not apply macro.");
        }
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    static Proof loadProof(String proofFileName) {
        File proofFile = new File(TEST_RESOURCES_DIR_PREFIX + proofFileName);
        assertTrue(proofFile.exists());

        try {
            KeYEnvironment<?> environment =
                    KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                            proofFile, null, null, null, true);
            Proof proof = environment.getLoadedProof();
            assertNotNull(proof);

            return proof;
        }
        catch (ProblemLoaderException e) {
            fail("Proof could not be loaded:\n" + e.getMessage());
            return null;
        }
    }

    private class IncompleteRuleAppException extends RuntimeException {
        private static final long serialVersionUID = 774109478701810300L;
    }

}
