/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.smt.testgen;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.*;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.testgen.TestCaseGenerator;
import de.uka.ilkd.key.testgen.TestgenUtils;
import de.uka.ilkd.key.testgen.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.testgen.macros.TestGenMacro;
import de.uka.ilkd.key.testgen.settings.TestGenerationSettings;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;
import org.key_project.util.collection.ImmutableList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.*;

/**
 * Implementations of this class are used generate test cases or a given {@link Proof}.
 * <p>
 * <b>This class provides the full logic independent from the a user interface.</b> Subclasses are
 * used to realize the user interface specific functionality.
 */
public abstract class AbstractTestGenerator {
    private static final Logger LOGGER = LoggerFactory.getLogger(AbstractTestGenerator.class);
    private final UserInterfaceControl ui;
    private final Proof originalProof;
    private SolverLauncher launcher;
    private List<Proof> proofs;

    /**
     * Constructor.
     *
     * @param ui            The {@link UserInterfaceControl} to use.
     * @param originalProof The {@link Proof} to generate test cases for.
     */
    protected AbstractTestGenerator(UserInterfaceControl ui, Proof originalProof) {
        this.ui = ui;
        this.originalProof = originalProof;
    }

    public void generateTestCases(final StopRequest stopRequest, final TestGenerationLog log) {


        TestGenerationSettings settings = TestGenerationSettings.getInstance();


        if (!SolverTypes.Z3_CE_SOLVER.isInstalled(true)) {
            log.writeln("Could not find the z3 SMT solver. Aborting.");
            return;
        }
        if (!SolverTypes.Z3_CE_SOLVER.isSupportedVersion()) {
            log.writeln("Warning: z3 supported minimum supported version is: "
                    + SolverTypes.Z3_CE_SOLVER.getMinimumSupportedVersion());
        }
        if (originalProof.closed() && settings.includePostCondition()) {
            log.writeln("Cannot generate test cases from closed proof with "
                    + "\nInclude Postcondition option activated. Aborting.");
            return;
        }

        if (settings.getApplySymbolicExecution()) {
            log.writeln("Applying TestGen Macro (bounded symbolic execution)...");
            try {
                TestGenMacro macro = new TestGenMacro();
                macro.applyTo(ui, originalProof, originalProof.openEnabledGoals(), null, null);
                log.writeln("Finished symbolic execution.");
            } catch (Exception ex) {
                log.writeException(ex);
            }
        }

        log.writeln("Extracting test data constraints (path conditions).");
        proofs =
                createProofsForTesting(settings.removeDuplicates(), !settings.includePostCondition());
        if (stopRequest != null && stopRequest.shouldStop()) {
            return;
        }
        if (!proofs.isEmpty()) {
            log.writeln("Extracted " + proofs.size() + " test data constraints.");
        } else {
            log.writeln("No test data constraints were extracted.");
        }
        final Collection<SMTProblem> problems = new LinkedList<>();
        log.writeln("Test data generation: applying semantic blasting macro on proofs");
        try {
            for (final Proof proof : proofs) {
                if (stopRequest != null && stopRequest.shouldStop()) {
                    return;
                }
                final SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
                TaskFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
                final ProverTaskListener ptl = ui.getProofControl().getDefaultProverTaskListener();
                try {
                    if (stopRequest != null && stopRequest.shouldStop()) {
                        return;
                    }

                    selectProof(ui, proof);

                    ptl.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));
                    info = macro.applyTo(ui, proof, proof.openEnabledGoals(), null, ptl);
                    problems.addAll(SMTProblem.createSMTProblems(proof));
                } catch (final InterruptedException e) {
                    LOGGER.debug("Semantics blasting interrupted");
                    log.writeln("\n Warning: semantics blasting was interrupted. "
                            + "A test case will not be generated.");
                } catch (final Exception e) {
                    log.writeln(e.getLocalizedMessage());
                    LOGGER.warn("", e);
                } finally {
                    ptl.taskFinished(info);
                }
            }
        } finally {
            handleAllProofsPerformed(ui);
        }
        log.writeln("\nDone applying semantic blasting.");
        selectProof(ui, originalProof);
        final Proof proof = originalProof;

        // create special smt settings for test case generation
        final ProofIndependentSMTSettings piSettings =
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().clone();
        piSettings.setMaxConcurrentProcesses(settings.getNumberOfProcesses());
        final ProofDependentSMTSettings pdSettings = proof.getSettings().getSMTSettings().clone();
        final NewSMTTranslationSettings newSettings =
                new NewSMTTranslationSettings(proof.getSettings().getNewSMTSettings());
        pdSettings.setInvariantForall(settings.invariantForAll());
        // invoke z3 for counterexamples
        final DefaultSMTSettings smtsettings =
                new DefaultSMTSettings(pdSettings, piSettings, newSettings, proof);
        launcher = new SolverLauncher(smtsettings);
        launcher.addListener(new SolverLauncherListener() {
            @Override
            public void launcherStopped(SolverLauncher launcher,
                                        Collection<SMTSolver> finishedSolvers) {
                handleLauncherStopped(launcher, finishedSolvers, log);
            }

            @Override
            public void launcherStarted(Collection<SMTProblem> problems,
                                        Collection<SolverType> solverTypes, SolverLauncher launcher) {
                handleLauncherStarted(problems, solverTypes, launcher, log);
            }
        });
        final List<SolverType> solvers = new LinkedList<>();
        solvers.add(SolverTypes.Z3_CE_SOLVER);
        SolverTypes.Z3_CE_SOLVER.checkForSupport();
        if (stopRequest != null && stopRequest.shouldStop()) {
            return;
        }
        if (Thread.interrupted()) {
            return;
        }
        launcher.launch(solvers, problems, proof.getServices());
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
     * Creates a proof for each open node if the selected proof is open and a proof for each node on
     * which the emptyModality rules was applied if the selected proof is closed.
     *
     * @param removeDuplicatePathConditions - if true no identical proofs will be created
     * @param removePostCondition           - if true, remove post condition
     * @return a list of proofs
     */
    private List<Proof> createProofsForTesting(boolean removeDuplicatePathConditions,
                                               boolean removePostCondition) {
        final List<Proof> res = new LinkedList<>();
        final List<Node> nodes = new LinkedList<>();
        final ImmutableList<Goal> oldGoals = originalProof.openGoals();
        if (originalProof.closed()) {
            getNodesWithEmptyModalities(originalProof.root(), nodes);
        } else {
            for (final Goal goal : oldGoals) {
                nodes.add(goal.node());
            }
        }
        final Iterator<Node> oldGoalIter = nodes.iterator();
        while (oldGoalIter.hasNext()) {
            try {
                Proof p;
                if (removeDuplicatePathConditions) {
                    p = createProofForTestingNoDuplicate(oldGoalIter.next(), res,
                            removePostCondition);
                } else {
                    p = createProofForTestingNoDuplicate(oldGoalIter.next(), null,
                            removePostCondition);
                }
                if (p != null) {
                    res.add(p);
                }
            } catch (final Exception e) {
                LOGGER.error("Could not create a proof for testing", e);
            }
        }
        return res;
    }

    /**
     * Adds all nodes on which the emptyModality rule was applied to the list.
     *
     * @param root  the root node
     * @param nodes the nodes to be added
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
     * Creates a proof with the specified node as its root. If an identical proof is found in
     * otherProofs than null will be returned instead.
     *
     * @param node                the new root node
     * @param otherProofs         a list of proofs as described above
     * @param removePostCondition if true, then remove post condition
     * @return the new proof with the specified root node
     * @throws ProofInputException exception for proof input
     */
    private Proof createProofForTestingNoDuplicate(Node node, List<Proof> otherProofs,
                                                   boolean removePostCondition) throws ProofInputException {
        final Proof oldProof = node.proof();
        final Sequent oldSequent = node.sequent();
        Sequent newSequent =
                Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT, Semisequent.EMPTY_SEMISEQUENT);
        Iterator<SequentFormula> it = oldSequent.antecedent().iterator();
        while (it.hasNext()) {
            final SequentFormula sf = it.next();
            // Allow updates modailities in the antecedent
            if (hasModalities(sf.formula(), false)) {
                continue;
            }
            newSequent = newSequent.addFormula(sf, true, false).sequent();
        }
        it = oldSequent.succedent().iterator();
        while (it.hasNext()) {
            final SequentFormula sf = it.next();
            if (hasModalities(sf.formula(), removePostCondition)) {
                continue;
            }
            newSequent = newSequent.addFormula(sf, false, false).sequent();
        }
        // Check if a proof with the same sequent already exists.
        if (otherProofs != null) {
            for (final Proof otherProof : otherProofs) {
                if (otherProof.root().sequent().equals(newSequent)) {
                    // Found and skip duplicate proof for node
                    return null;
                }
            }
        }
        return createProof(ui, oldProof, "Test Case for NodeNr: " + node.serialNr(), newSequent);
    }

    protected Proof createProof(UserInterfaceControl ui, Proof oldProof, String newName,
                                Sequent newSequent) throws ProofInputException {
        ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(oldProof,
                new Choice("ban", "runtimeExceptions"));
        ProofStarter starter = SideProofUtil.createSideProof(env, newSequent, newName);
        Proof proof = starter.getProof();
        proof.getServices().getSpecificationRepository().registerProof(
                proof.getServices().getSpecificationRepository().getProofOblInput(oldProof), proof);
        OneStepSimplifier.refreshOSS(proof);
        return proof;
    }

    private boolean hasModalities(Term t, boolean checkUpdates) {
        final JavaBlock jb = t.javaBlock();
        if (!jb.isEmpty()) {
            return true;
        }
        if (t.op() == UpdateApplication.UPDATE_APPLICATION && checkUpdates) {
            return true;
        }
        boolean res = false;
        for (int i = 0; i < t.arity() && !res; i++) {
            res = hasModalities(t.sub(i), checkUpdates);
        }
        return res;
    }


    protected void handleLauncherStarted(Collection<SMTProblem> problems,
                                         Collection<SolverType> solverTypes, SolverLauncher launcher, TestGenerationLog log) {
        log.writeln("Test data generation: solving " + problems.size()
                + " SMT problems... \n please wait...");
    }

    protected void handleLauncherStopped(SolverLauncher launcher,
                                         Collection<SMTSolver> problemSolvers, TestGenerationLog log) {
        try {
            log.writeln("Finished solving SMT problems: " + problemSolvers.size());
            problemSolvers = filterSolverResultsAndShowSolverStatistics(problemSolvers, log);
            if (!problemSolvers.isEmpty()) {
                generateFiles(problemSolvers, log, originalProof);
            } else {
                log.writeln("No test data was generated.");
                informAboutNoTestResults(launcher, problemSolvers, log, originalProof);
            }
            log.testGenerationCompleted();
        } catch (Exception e) {
            log.writeException(e);
        }
    }

    protected void generateFiles(Collection<SMTSolver> problemSolvers, TestGenerationLog log, Proof originalProof) throws IOException {
        final TestCaseGenerator tg = new TestCaseGenerator(originalProof, new TestGenerationSettings(), log);
        tg.generateJUnitTestSuite(problemSolvers);
        if (tg.isJunit()) {
            log.writeln("Compile the generated files using a Java compiler.");
        } else {
            log.writeln("Compile and run the file with openjml!");
        }
    }

    /**
     * This method is used in the Eclipse world to show a dialog with the log.
     */
    protected void informAboutNoTestResults(SolverLauncher launcher,
                                            Collection<SMTSolver> problemSolvers, TestGenerationLog log, Proof originalProof) {
    }

    public Collection<SMTSolver> filterSolverResultsAndShowSolverStatistics(
            Collection<SMTSolver> problemSolvers, TestGenerationLog log) {
        int unknown = 0;
        int infeasiblePaths = 0;
        int solvedPaths = 0;
        int problem = 0;
        final List<SMTSolver> output = new ArrayList<>();
        for (final SMTSolver solver : problemSolvers) {
            try {
                final SMTSolverResult.ThreeValuedTruth res = solver.getFinalResult().isValid();
                if (res == SMTSolverResult.ThreeValuedTruth.UNKNOWN) {
                    unknown++;
                    if (solver.getException() != null) {
                        LOGGER.warn("Solver returned exception", solver.getException());
                    }
                } else if (res == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE) {
                    solvedPaths++;
                    if (solver.getSocket().getQuery() != null) {
                        final Model m = solver.getSocket().getQuery().getModel();
                        if (TestgenUtils.modelIsOK(m)) {
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
        log.writeln("--- SMT Solver Results ---\n" + " solved pathconditions:" + solvedPaths + "\n"
                + " invalid pre-/pathconditions:" + infeasiblePaths + "\n" + " unknown:" + unknown);
        if (problem > 0) {
            log.writeln(" problems             :" + problem);
        }
        if (unknown > 0) {
            log.writeln(
                    " Adjust the SMT solver settings (e.g. timeout) in Options->SMT Solvers and restart key.\n Make sure you use Z3 version 4.3.1.");
        }
        log.writeln("----------------------");
        return output;
    }

    public void stopSMTLauncher() {
        if (launcher != null) {
            launcher.stop();
        }
    }

    protected Proof getOriginalProof() {
        return originalProof;
    }

    protected List<Proof> getProofs() {
        return proofs;
    }

    protected UserInterfaceControl getUI() {
        return ui;
    }

    /**
     * Checks if the required SMT solver is available.
     *
     * @return {@code true} solver is available, {@code false} solver is not available.
     */
    public static boolean isSolverAvailable() {
        return SolverTypes.Z3_CE_SOLVER.isInstalled(true);
    }
}
