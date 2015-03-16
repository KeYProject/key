package de.uka.ilkd.key.smt.testgen;

import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.settings.TestGenerationSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.testgen.TestCaseGenerator;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

/**
 * Implementations of this class are used generate test cases or a given {@link Proof}.
 * <p>
 * <b>This class provides the full logic independent from the a user interface.</b>
 * Subclasses are used to realize the user interface specific functionality.
 */
public abstract class AbstractTestGenerator {
   private final UserInterfaceControl ui;
   private final Proof originalProof;
   private SolverLauncher launcher;
   private List<Proof> proofs;
   
   /**
    * Constructor.
    * @param ui The {@link UserInterfaceControl} to use.
    * @param originalProof The {@link Proof} to generate test cases for.
    */
   public AbstractTestGenerator(UserInterfaceControl ui, Proof originalProof) {
      this.ui = ui;
      this.originalProof = originalProof;
   }

   public void generateTestCases(final StopRequest stopRequest,
                                 final TestGenerationLog log) {
      TestGenerationSettings settings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();


    if (!SolverType.Z3_CE_SOLVER.isInstalled(true)) {
       log
       .writeln("Could not find the z3 SMT solver. Aborting.");
       return;
    }
    if (!SolverType.Z3_CE_SOLVER.isSupportedVersion()) {
       log.writeln("Warning: z3 supported versions are: "
             + Arrays.toString(SolverType.Z3_CE_SOLVER
                   .getSupportedVersions()));
    }
    log
    .writeln("Extracting test data constraints (path conditions).");
    proofs = createProofsForTesting(settings.removeDuplicates());
    if (stopRequest != null && stopRequest.shouldStop()) {
       return;
    }
    if (proofs.size() > 0) {
       log.writeln("Extracted " + proofs.size()
             + " test data constraints.");
    } else {
       log
       .writeln("No test data constraints were extracted.");
    }
    final Collection<SMTProblem> problems = new LinkedList<SMTProblem>();
    log
    .writeln("Test data generation: appling semantic blasting macro on proofs");
    try {
       for (final Proof proof : proofs) {
          if (stopRequest != null && stopRequest.shouldStop()) {
             return;
          }
          log.write(".");
          final SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
          TaskFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
          final ProverTaskListener ptl = ui.getProofControl().getDefaultProverTaskListener();
          try {
             if (stopRequest != null && stopRequest.shouldStop()) {
                return;
             }
             selectProof(ui, proof);

             ptl.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));
             synchronized(macro) {
                          info = macro.applyTo(ui, proof, proof.openEnabledGoals(), null, ptl);
             }
             problems.addAll(SMTProblem.createSMTProblems(proof));
          } catch (final InterruptedException e) {
             Debug.out("Semantics blasting interrupted");
             log
             .writeln("\n Warning: semantics blasting was interrupted. "
                      + "A test case will not be generated.");
          } catch (final Exception e) {
             log.writeln(e.getLocalizedMessage());
             System.err.println(e);
          } finally {
              ptl.taskFinished(info);
          }
       }
    }
    finally {
       handleAllProofsPerformed(ui);
    }
    log.writeln("\nDone applying semantic blasting.");
    selectProof(ui, originalProof);
    // getMediator().setInteractive(true);
    // getMediator().startInterface(true);
    final Proof proof = originalProof;

    //create special smt settings for test case generation
    final ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE
          .getSMTSettings().clone();
    piSettings.setMaxConcurrentProcesses(settings.getNumberOfProcesses());
    final ProofDependentSMTSettings pdSettings = proof.getSettings()
          .getSMTSettings().clone();
    pdSettings.invariantForall = settings.invaraiantForAll();
    // invoke z3 for counterexamples
    final SMTSettings smtsettings = new SMTSettings(pdSettings,
          piSettings, proof);
    launcher = new SolverLauncher(smtsettings);
    launcher.addListener(new SolverLauncherListener() {
       @Override
       public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {
          handleLauncherStopped(launcher, finishedSolvers, log);
       }
       
       @Override
       public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes, SolverLauncher launcher) {
          handleLauncherStarted(problems, solverTypes, launcher, log);
       }
    });
    // launcher.addListener(new SolverListener(settings));
    final List<SolverType> solvers = new LinkedList<SolverType>();
    solvers.add(SolverType.Z3_CE_SOLVER);
    SolverType.Z3_CE_SOLVER.checkForSupport();
    if (stopRequest != null && stopRequest.shouldStop()) {
       return;
    }
    if (Thread.interrupted()) {
       return;
    }
    launcher.launch(solvers, problems, proof.getServices());
    //    ModelGenerator mg = new ModelGenerator(proofs.get(0).root().sequent(), 3, getMediator());
    //    mg.launch();
    return;
   }

   protected void handleAllProofsPerformed(UserInterfaceControl ui) {
      // Work has only to be done in the MainWindow implementation.
   }

   /**
    * Removes all generated proofs.
    */
   public void dispose() {
      if (proofs != null) {
         for (final Proof p : proofs) {
            p.dispose();
         }
      }
   }

   protected void selectProof(UserInterfaceControl ui, Proof proof) {
      // Work has only to be done in the MainWindow implementation.
   }

   /**
    * Creates a proof for each open node if the selected proof is open and a
    * proof for each node on which the emptyModality rules was applied if the
    * selected proof is closed.
    * 
    * @param mediator
    * @param removeDuplicatePathConditions
    *            - if true no identical proofs will be created
    * @return
    */
   private List<Proof> createProofsForTesting(boolean removeDuplicatePathConditions) {
      final List<Proof> res = new LinkedList<Proof>();
      final List<Node> nodes = new LinkedList<Node>();
      final ImmutableList<Goal> oldGoals = originalProof.openGoals();
      if (originalProof.closed()) {
         getNodesWithEmptyModalities(
               originalProof.root(), nodes);
      } else {
         for (final Goal goal : oldGoals) {
            nodes.add(goal.node());
         }
      }
      final Iterator<Node> oldGoalIter = nodes.iterator();
      while (oldGoalIter.hasNext()) {
         try {
            Proof p = null;
            if (removeDuplicatePathConditions) {
               p = createProofForTesting_noDuplicate(oldGoalIter.next(),
                     res);
            } else {
               p = createProofForTesting_noDuplicate(oldGoalIter.next(),
                     null);
            }
            if (p != null) {
               res.add(p);
            }
         } catch (final Exception e) {
            System.err.println(e.getMessage());
         }
      }
      return res;
   }

   /**
    * Adds all nodes on which the emptyModality rule was applied to the list.
    * 
    * @param root
    * @param nodes
    */
   private void getNodesWithEmptyModalities(Node root, List<Node> nodes) {
      if (root.getAppliedRuleApp() != null) {
         final RuleApp app = root.getAppliedRuleApp();
         if (app.rule().name().toString().equals("emptyModality")) {
            nodes.add(root);
         }
      }
      for (int i = 0; i < root.childrenCount(); ++i) {
         getNodesWithEmptyModalities(root.child(i), nodes);
      }
   }

   /**
    * Creates a proof with the specified node as its root. If an identical
    * proof is found in otherProofs than null will be returned instead.
    * 
    * @param node
    * @param otherProofs
    * @return
    * @throws ProofInputException 
    */
   private Proof createProofForTesting_noDuplicate(Node node, List<Proof> otherProofs) throws ProofInputException {
      // System.out.println("Create proof for test case from Node:"+node.serialNr());
      final Proof oldProof = node.proof();
      final Sequent oldSequent = node.sequent();
      Sequent newSequent = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT, Semisequent.EMPTY_SEMISEQUENT);
      Iterator<SequentFormula> it = oldSequent.antecedent().iterator();
      while (it.hasNext()) {
         final SequentFormula sf = it.next();
         // Allow modailities in the antecedent
         if (hasModalities(sf.formula(), false)) {
            continue;
         }
         newSequent = newSequent.addFormula(sf, true, false).sequent();
      }
      it = oldSequent.succedent().iterator();
      while (it.hasNext()) {
         final SequentFormula sf = it.next();
         if (hasModalities(sf.formula(), true)) {
            continue;
         }
         newSequent = newSequent.addFormula(sf, false, false).sequent();
      }
      // Check if a proof with the same sequent already exists.
      if (otherProofs != null) {
         for (final Proof otherProof : otherProofs) {
            if (otherProof.root().sequent().equals(newSequent)) {
               // System.out.println("Found and skip duplicate proof for node:"+node.serialNr());
               return null;
            }
         }
      }  
      return createProof(ui, oldProof, "Test Case for NodeNr: " + node.serialNr(), newSequent);
   }
   
   protected Proof createProof(UserInterfaceControl ui, Proof oldProof, String newName, Sequent newSequent) throws ProofInputException {
      ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(oldProof);
      ProofStarter starter = SideProofUtil.createSideProof(env, newSequent, newName);
      Proof proof = starter.getProof();
      proof.getServices().getSpecificationRepository().registerProof(proof.getServices().getSpecificationRepository().getProofOblInput(oldProof), proof);
      OneStepSimplifier.refreshOSS(proof);
      return proof;
   }

   private boolean hasModalities(Term t, boolean checkUpdates) {
      final JavaBlock jb = t.javaBlock();
      if (jb != null && !jb.isEmpty()) {
         // System.out.println("Excluded javablock");
         return true;
      }
      if (t.op() == UpdateApplication.UPDATE_APPLICATION && checkUpdates) {
         // System.out.println("Exclude update application.");
         return true;
      }
      boolean res = false;
      for (int i = 0; i < t.arity() && !res; i++) {
         res |= hasModalities(t.sub(i), checkUpdates);
      }
      return res;
   }


   protected void handleLauncherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes, SolverLauncher launcher, TestGenerationLog log) {
      log.writeln("Test data generation: solving SMT problems... \n please wait...");
   }

   protected void handleLauncherStopped(SolverLauncher launcher, Collection<SMTSolver> problemSolvers, TestGenerationLog log) {
      try {
         log.writeln("Finished solving SMT problems: " + problemSolvers.size());
         problemSolvers = filterSolverResultsAndShowSolverStatistics(problemSolvers, log);
         if (problemSolvers.size() > 0) {
            generateFiles(launcher, problemSolvers, log, originalProof);
         } else {
            log.writeln("No test data was generated.");
            informAboutNoTestResults(launcher, problemSolvers, log, originalProof);
         }
         log.testGenerationCompleted();
      }
      catch (Exception e) {
         log.writeException(e);
      }
   }

   protected void generateFiles(SolverLauncher launcher, Collection<SMTSolver> problemSolvers, TestGenerationLog log, Proof originalProof) throws Exception {
      final TestCaseGenerator tg = new TestCaseGenerator(originalProof);
      tg.setLogger(log);
      tg.generateJUnitTestSuite(problemSolvers);
      if (tg.isJunit()) {
         log.writeln("Test oracle not yet implemented for JUnit.");
      } else {
         log.writeln("Compile and run the file with openjml!");
      }
   }

   /**
    * This method is used in the Eclipse world to show a dialog with the log.
    */
   protected void informAboutNoTestResults(SolverLauncher launcher, Collection<SMTSolver> problemSolvers, TestGenerationLog log, Proof originalProof) {
   }

   public Collection<SMTSolver> filterSolverResultsAndShowSolverStatistics(Collection<SMTSolver> problemSolvers, TestGenerationLog log) {
      int unknown = 0;
      int infeasiblePaths = 0;
      int solvedPaths = 0;
      int problem = 0;
      final Vector<SMTSolver> output = new Vector<SMTSolver>();
      for (final SMTSolver solver : problemSolvers) {
         try {
            final SMTSolverResult.ThreeValuedTruth res = solver
                    .getFinalResult().isValid();
            if (res == SMTSolverResult.ThreeValuedTruth.UNKNOWN) {
               unknown++;
            } else if (res == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE) {
               solvedPaths++;
               if (solver.getSocket().getQuery() != null) {
                  final Model m = solver.getSocket().getQuery()
                          .getModel();
                  if (TestCaseGenerator.modelIsOK(m)) {
                     output.add(solver);
                  } else {
                     problem++;
                  }
               } else {
                  problem++;
               }
            } else if (res == SMTSolverResult.ThreeValuedTruth.VALID) {
               infeasiblePaths++;
            }
         } catch (final Exception ex) {
            log.writeln(ex.getMessage());
         }
      }
      log.writeln("--- SMT Solver Results ---\n" + " solved pathconditions:"
              + solvedPaths + "\n" + " invalid pre-/pathconditions:"
              + infeasiblePaths + "\n" + " unknown:" + unknown);
      if (problem > 0) {
         log.writeln(" problems             :" + problem);
      }
      if (unknown > 0) {
         log.writeln(" Adjust the SMT solver settings (e.g. timeout) in Options->SMT Solvers and restart key.\n Make sure you use Z3 version 4.3.1.");
      }
      log.writeln("----------------------");
      return output;
   }
   
   public void stopSMTLauncher() {
      if (launcher != null) {
         launcher.stop();
      }
   }

   protected Proof getOriginalProof(){
      return originalProof;
   }

   protected List<Proof> getProofs() {
      return proofs;
   }
   
   protected UserInterfaceControl getUI () {
      return ui;
   }

   /**
    * Checks if the required SMT solver is available.
    * @return {@code true} solver is available, {@code false} solver is not available.
    */
   public static boolean isSolverAvailable() {
      return SolverType.Z3_CE_SOLVER.isInstalled(true);
   }
}
