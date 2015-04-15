package de.uka.ilkd.key.util;

import java.io.File;

import junit.framework.TestCase;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Tests for {@link ProofStarter}.
 * @author Martin Hentschel
 */
public class TestProofStarter extends TestCase {
   /**
    * Loads key-file {@code examples/_testcase/proofStarter/CC/project.key}
    * and runs the auto mode via {@link ProofStarter} 
    * while one step simplification is disabled.
    * @throws ProblemLoaderException Occurred Exception
    */
   public void testDirectProof() throws ProblemLoaderException {
      doProofStarter(false);
   }
   
   /**
    * Loads key-file {@code examples/_testcase/proofStarter/CC/project.key}
    * and runs the auto mode via {@link ProofStarter} 
    * while one step simplification is enabled.
    * @throws ProblemLoaderException Occurred Exception
    */
   public void testDirectProofWithOneStepSimplification() throws ProblemLoaderException {
      doProofStarter(true);
   }
   
   /**
    * Executes the test steps of {@link #testDirectProof()}
    * and {@link #testDirectProofWithOneStepSimplification()}.
    * @param oneStepSimplification Use one step simplification?
    * @throws ProblemLoaderException Occurred Exception
    */
   protected void doProofStarter(boolean oneStepSimplification) throws ProblemLoaderException {
      KeYEnvironment<DefaultUserInterfaceControl> env = null;
      boolean originalOneStepSimplification = HelperClassForTests.isOneStepSimplificationEnabled(null);
      try {
         File file = new File(HelperClassForTests.TESTCASE_DIRECTORY, "proofStarter/CC/project.key");
         env = KeYEnvironment.load(file, null, null, null);
         Proof proof = env.getLoadedProof();
         assertNotNull(proof);
         ProofStarter ps = new ProofStarter(false);
         ps.init(proof);
         HelperClassForTests.setOneStepSimplificationEnabled(proof, oneStepSimplification);
         ApplyStrategyInfo info = ps.start();
         assertNotNull(info);
         assertTrue(proof.closed());
      }
      finally {
         HelperClassForTests.setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         if (env != null) {
            env.dispose();
         }
      }
   }
}
