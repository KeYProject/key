package de.uka.ilkd.key.util;

import java.io.File;

import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Tests for {@link ProofStarter}.
 * @author Martin Hentschel
 */
public class TestProofStarter extends AbstractSymbolicExecutionTestCase {
   /**
    * Loads key-file {@code examples/_testcase/proofStarter/CC/project.key}
    * and runs the auto mode via {@link ProofStarter} 
    * while one step simplification is disabled.
    */
   public void testDirectProof() {
      doProofStarter(false);
   }
   
   /**
    * Loads key-file {@code examples/_testcase/proofStarter/CC/project.key}
    * and runs the auto mode via {@link ProofStarter} 
    * while one step simplification is enabled.
    */
   public void testDirectProofWithOneStepSimplification() {
      doProofStarter(true);
   }
   
   /**
    * Executes the test steps of {@link #testDirectProof()}
    * and {@link #testDirectProofWithOneStepSimplification()}.
    * @param oneStepSimplification
    */
   protected void doProofStarter(boolean oneStepSimplification) {
      KeYEnvironment<CustomConsoleUserInterface> env = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         File file = new File(keyRepDirectory, "examples/_testcase/proofStarter/CC/project.key");
         env = KeYEnvironment.load(file, null, null);
         Proof proof = env.getLoadedProof();
         assertNotNull(proof);
         ProofStarter ps = new ProofStarter(false);
         ps.init(proof);
         setOneStepSimplificationEnabled(proof, oneStepSimplification);
         ApplyStrategyInfo info = ps.start();
         assertNotNull(info);
         assertTrue(proof.closed());
      }
      finally {
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         if (env != null) {
            env.dispose();
         }
      }
   }
}
