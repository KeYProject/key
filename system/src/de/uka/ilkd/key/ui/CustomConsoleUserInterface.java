package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;

/**
 * <p>
 * An extended version of {@link ConsoleUserInterface} which can be used
 * to prove manually instantiated proofs.
 * </p>
 * <p>
 * The basic usage is like:
 * <code><pre>
 * // Create user interface
 * CustomConsoleUserInterface ui = new CustomConsoleUserInterface(false);
 * // Load java file
 * InitConfig initConfig = ui.load(javaFile, null, null);
 * // Find operation contract to proof in services
 * Services services = initConfig.getServices();
 * FunctionalOperationContract contract ...
 * // Start proof
 * ProofOblInput input = new FunctionalOperationContractPO(initConfig, contract);
 * Proof proof = ui.createProof(initConfig, input);
 * // Run proof in auto mode
 * ui.startAndWaitForProof(proof);
 * </pre></code>
 * </p>
 * @author Martin Hentschel
 */
public class CustomConsoleUserInterface extends ConsoleUserInterface {
   /**
    * Constructor.
    * @param verbose Verbose?
    */
   public CustomConsoleUserInterface(boolean verbose) {
      super(null, verbose);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void proofCreated(ProblemInitializer sender, ProofAggregate proofAggregate) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void taskStarted(String message, int size) {
      if(isVerbose()) {
         System.out.println("CustomConsoleUserInterface.taskStarted(" + message + "," + size + ")");
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void taskFinished(TaskFinishedInfo info) {
      if(isVerbose()) {
         System.out.println("CustomConsoleUserInterface.taskFinished()");
      }
   }
}