/**
 * 
 */
package de.uka.ilkd.key.rule.join;

import java.io.File;

import junit.framework.TestCase;

import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionUntilJoinPointMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.join.procedures.JoinIfThenElseAntecedent;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * Test suite for the join rule.
 *
 * @author Dominic Scheurer
 */
public class JoinRuleTests extends TestCase {

    private static final String TEST_RESOURCES_DIR_PREFIX = "resources/testcase/join/";

    /**
     * Simple regression test case loading an existing closed proof (standard
     * Gcd example) including two joins and trying to replay it.
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
            runSymbExMacro(proof.openGoals().head().node());
            joinFirstGoal(proof);
        }

        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    /**
     * Runs the automatic JavaDL strategy on the given proof.
     *
     * @param proof Proof to prove automatically.
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
    private void joinFirstGoal(final Proof proof) {
        final Services services = proof.getServices();
        final JoinRule joinRule = JoinRule.INSTANCE;

        final Goal joinGoal = proof.openGoals().head();
        final Node joinNode = joinGoal.node();
        final PosInOccurrence joinPio = getPioFirstFormula(joinNode.sequent());
        final JoinRuleBuiltInRuleApp joinApp = (JoinRuleBuiltInRuleApp) joinRule
                .createApp(joinPio, services);

        {
            joinApp.setJoinPartners(JoinRule.findPotentialJoinPartners(proof
                    .openGoals().head(), joinPio));
            joinApp.setConcreteRule(JoinIfThenElseAntecedent.instance());
            joinApp.setJoinNode(joinNode);
        }

        assertTrue(joinApp.complete());
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
     * Runs the {@link FinishSymbolicExecutionUntilJoinPointMacro} on the given
     * proof node.
     *
     * @param node
     *            The node to execute the macro on.
     */
    private void runSymbExMacro(Node node) {
        try {
            new FinishSymbolicExecutionUntilJoinPointMacro().applyTo(null,
                    node, null, null);
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
    private Proof loadProof(String proofFileName) {
        File proofFile = new File(TEST_RESOURCES_DIR_PREFIX + proofFileName);
        assertTrue(proofFile.exists());

        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
            Proof proof = environment.getLoadedProof();
            assertNotNull(proof);

            return proof;
        }
        catch (ProblemLoaderException e) {
            fail("Proof could not be loaded.");
            return null;
        }
    }

}
