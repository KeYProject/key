package de.uka.ilkd.key.ui;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;

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
    * Indicates that a task is active.
    */
   private boolean taskActive;

   /**
    * Constructor.
    * @param verbose Verbose?
    */
   public CustomConsoleUserInterface(boolean verbose) {
      super(null, verbose);
   }
   
   /**
    * Opens a java file.
    * @param file The java file to open.
    * @param classPath The class path entries to use.
    * @param bootClassPath The boot class path to use.
    * @return The opened {@link InitConfig}.
    * @throws FileNotFoundException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   public InitConfig load(File file, List<File> classPath, File bootClassPath) throws FileNotFoundException, ProofInputException {
      ProblemLoader loader = new ProblemLoader(file, classPath, bootClassPath, getMediator());
      EnvInput envInput = loader.createEnvInput(file, classPath, bootClassPath);
      ProblemInitializer init = createProblemInitializer();
      return init.prepare(envInput);
   }
   
   /**
    * Instantiates a new {@link Proof} instance for the given {@link ProofOblInput}.
    * @param initConfig The {@link InitConfig} to use.
    * @param input The {@link ProofOblInput} to instantiate {@link Proof} for.
    * @return The instantiated {@link Proof}.
    * @throws ProofInputException Occurred Exception.
    */
   public Proof createProof(InitConfig initConfig, ProofOblInput input) throws ProofInputException {
      return createProblemInitializer().startProver(initConfig, input);
   }
   
   /**
    * Starts the auto mode for the given proof which must be contained
    * in this user interface and blocks the current thread until it
    * has finished.
    * @param proof The {@link Proof} to start auto mode and to wait for.
    */
   public void startAndWaitForProof(Proof proof) {
      startProof(proof);
      waitWhileActive();
   }
   
   /**
    * Starts the auto mode for the given proof which must be contained in this
    * user interface.
    * @param proof The proof to start auto mode for.
    */
   public void startProof(Proof proof) {
      setTaskActive(true); // Will be unset automatically when the auto mode has stopped.
      KeYMediator mediator = getMediator();
      mediator.setProof(proof);
      mediator.startAutoMode();
   }
   
   /**
    * Blocks the current thread until {@link #isTaskActive()} is {@code false}.
    */
   public void waitWhileActive() {
      while (isTaskActive()) { // Wait until auto mode has stopped.
         try {
            Thread.sleep(10);
         }
         catch (InterruptedException e) {
         }
      }
   }

   /**
    * Checks if a task is active.
    * @return {@code true} task is active, {@code false} no task is active.
    */
   public boolean isTaskActive() {
      return taskActive;
   }

   /**
    * Defines if a task is active. 
    * This should be done programmatically before the auto mode thread
    * started to simplify the waiting process.
    * @param taskActive {@code true} task is active, {@code false} no task is active.
    */
   public void setTaskActive(boolean taskActive) {
      this.taskActive = taskActive;
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
      taskActive = false;
      if(isVerbose()) {
         System.out.println("CustomConsoleUserInterface.taskFinished()");
      }
   }
}