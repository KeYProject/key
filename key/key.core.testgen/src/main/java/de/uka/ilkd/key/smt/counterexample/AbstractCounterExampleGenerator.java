package de.uka.ilkd.key.smt.counterexample;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.util.Debug;

/**
 * Implementations of this class are used find a counter example for a given
 * {@link Sequent} using the SMT solver {@link SolverType#Z3_CE_SOLVER}.
 * <p>
 * <b>This class provides the full logic independent from the a user interface.</b>
 * Subclasses are used to realize the user interface specific functionality.
 * <p>
 * When {@link #searchCounterExample(KeYMediator, Proof, Sequent)} is called
 * a new {@link Proof} is instantiated by {@link #createProof(KeYMediator, Proof, Sequent)}.
 * Next the macro {@link SemanticsBlastingMacro} is performed on the new {@link Proof}
 * and when done the SMT solver is started. The progress of the SMT solver and
 * the final result can be observed by a {@link SolverLauncherListener} instantiated.
 * by {@link #createSolverListener(SMTSettings)}.
 */
public abstract class AbstractCounterExampleGenerator {
   /**
    * Checks if the required SMT solver is available.
    * @return {@code true} solver is available, {@code false} solver is not available.
    */
   public static boolean isSolverAvailable() {
      return SolverType.Z3_CE_SOLVER.isInstalled(true);
   }
   
   /**
    * Searches a counter example for the given {@link Sequent}.
    * @param ui The {@link UserInterfaceControl} to use.
    * @param oldProof The old {@link Proof} used as template to instantiate a new one.
    * @param oldSequent The {@link Sequent} to find a counter example for.
    * @throws ProofInputException Occurred Exception.
    */
   public void searchCounterExample(UserInterfaceControl ui, 
                                    Proof oldProof, 
                                    Sequent oldSequent) throws ProofInputException {
      if (!isSolverAvailable()) {
         throw new IllegalStateException("Can't find SMT solver " + SolverType.Z3_CE_SOLVER.getName());
      }
      
      final Proof proof = createProof(ui, oldProof, oldSequent, "Semantics Blasting: " + oldProof.name());
      final SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
      TaskFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
      final ProverTaskListener ptl = ui.getProofControl().getDefaultProverTaskListener();
      ptl.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));

      try {
          synchronized(macro) { // TODO: Useless? No other thread has access to macro wait for macro to terminate
              info = macro.applyTo(ui, proof, proof.openEnabledGoals(), null, ptl);
          }
      } catch (InterruptedException e) {
          Debug.out("Semantics blasting interrupted");
      } finally {
          semanticsBlastingCompleted(ui);
          ptl.taskFinished(info);
      }

      //invoke z3 for counterexamples
      SMTSettings settings = new SMTSettings(proof.getSettings().getSMTSettings(),
              ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(), proof);
      SolverLauncher launcher = new SolverLauncher(settings);
      launcher.addListener(createSolverListener(settings, proof));

      List<SolverType> solvers = new LinkedList<SolverType>();
      solvers.add(SolverType.Z3_CE_SOLVER);

      launcher.launch(solvers,
              SMTProblem.createSMTProblems(proof),
              proof.getServices());

      
   }
   
   /**
    * Creates a new {@link Proof}.
    * @param ui The {@link UserInterfaceControl} to use.
    * @param oldProof The old {@link Proof} used as template to instantiate a new one.
    * @param oldSequent The {@link Sequent} to find a counter example for.
    * @param proofName The name for the new proof.
    * @return The created {@link Proof}.
    * @throws ProofInputException Ocurred Exception
    */
   protected abstract Proof createProof(UserInterfaceControl ui, 
                                        Proof oldProof, 
                                        Sequent oldSequent,
                                        String proofName) throws ProofInputException;

   
   /**
    * Creates the {@link Sequent} for the new {@link Proof} created by 
    * {@link #createProof(KeYMediator, Proof, Sequent)}.
    * @param oldSequent The {@link Sequent} to find a counter example for.
    * @return The new {@link Sequent}.
    */
   protected Sequent createNewSequent(Sequent oldSequent) {
      return Sequent.createSequent(oldSequent.antecedent(), oldSequent.succedent());
   }
   
   /**
    * This method is called after the {@link SemanticsBlastingMacro} has been executed.
    * @param ui The {@link UserInterfaceControl} to use.
    */
   protected void semanticsBlastingCompleted(UserInterfaceControl ui) {
   }
   
   /**
    * Creates the {@link SolverLauncherListener} which handles the results
    * of the launched SMT solver.
    * @param settings The {@link SMTSettings}.
    * @param proof The {@link Proof} on which the SMT solver will be performed.
    * @return The {@link SolverLauncherListener} to use.
    */
   protected abstract SolverLauncherListener createSolverListener(SMTSettings settings, Proof proof);
}