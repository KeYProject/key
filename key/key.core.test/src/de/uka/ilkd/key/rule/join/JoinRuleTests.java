/**
 * 
 */
package de.uka.ilkd.key.rule.join;

import java.io.File;

import junit.framework.TestCase;

import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Test suite for the join rule.
 *
 * @author Dominic Scheurer
 */
public class JoinRuleTests extends TestCase {

    /**
     * Simple regression test case loading an existing closed proof (standard
     * Gcd example) and trying to replay it.
     *
     * @throws ProblemLoaderException If the proof could not be loaded.
     */
    @Test
    public void testLoadGcdProof() throws ProblemLoaderException {
        File proofFile = new File("resources/testcase/join/gcd.closed.proof");
        assertTrue(proofFile.exists());

        KeYEnvironment<?> environment = KeYEnvironment.load(
                JavaProfile.getDefaultInstance(), proofFile, null, null, null,
                true);
        Proof proof = environment.getLoadedProof();
        assertNotNull(proof);

        assertTrue(proof.closed());
    }

}
