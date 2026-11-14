/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.testgen;

import java.io.IOException;
import java.util.Collection;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.concurrent.Callable;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.testgen.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.testgen.macros.TestGenMacro;
import de.uka.ilkd.key.testgen.smt.testgen.TGPhase;
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLifecycleListener;

import org.key_project.prover.engine.ProverTaskListener;

public record TestgenFacade(TestGenerationSettings settings) {
    public static Callable<Boolean> generateTestcasesTask(KeYEnvironment<?> env, Proof proof,
            TestGenerationSettings settings,
            TestGenerationLifecycleListener log) {
        return () -> {
            generateTestcases(env, proof, settings, log);
            return true;
        };
    }

    public static void generateTestcases(KeYEnvironment<?> env, Proof proof,
            TestGenerationSettings settings,
            TestGenerationLifecycleListener log) throws Exception {
        final TGReporter reporter = new TGReporter(log);

        final TestCaseGenerator tg = new TestCaseGenerator(proof, settings, reporter);

        NewSMTTranslationSettings newSettings = new NewSMTTranslationSettings();
        ProofDependentSMTSettings pdSettings = ProofDependentSMTSettings.getDefaultSettingsData();
        ProofIndependentSMTSettings piSettings =
            ProofIndependentSMTSettings.getDefaultSettingsData();

        piSettings.setTimeout(10000);
        final var smtSettings = new DefaultSMTSettings(pdSettings, piSettings, newSettings, proof);

        var launcher = new SolverLauncher(smtSettings);
        launcher.addListener(new SolverLauncherListener() {
            @Override
            public void launcherStopped(SolverLauncher launcher,
                    Collection<SMTSolver> finishedSolvers) {
                try {
                    var first = finishedSolvers.iterator().next();
                    if (first.getException() != null) {
                        throw new RuntimeException("Exception during SMT", first.getException());
                    }

                    tg.generateJUnitTestSuite(finishedSolvers);
                    reporter.writeln("Compile the generated files using a Java compiler.");
                } catch (NoSuchElementException | IOException e) {
                    reporter.reportException(e);
                }
            }

            @Override
            public void launcherStarted(Collection<SMTProblem> problems,
                    Collection<SolverType> solverTypes, SolverLauncher launcher) {
            }
        });

        SolverType z3ce = SolverTypes.Z3_CE_SOLVER;
        if (z3ce == null) {
            throw new NullPointerException("Z3 counter-example solver is not registered.");
        }
        final List<SolverType> solvers = List.of(z3ce);
        final ProverTaskListener ptl = env.getUi().getProofControl().getDefaultProverTaskListener();

        if (settings.getApplySymbolicExecution()) {
            final ProofMacro symbex = new FinishSymbolicExecutionMacro();
            symbex.applyTo(env.getUi(), proof, proof.openEnabledGoals(), null, ptl);
        }

        final ProofMacro tgMacro = new TestGenMacro(settings.getMaximalUnwinds());
        tgMacro.applyTo(env.getUi(), proof, proof.openEnabledGoals(), null, ptl);

        final ProofMacro macro = new SemanticsBlastingMacro();
        macro.applyTo(env.getUi(), proof, proof.openEnabledGoals(), null, ptl);

        final Collection<SMTProblem> problems = SMTProblem.createSMTProblems(proof);
        launcher.launch(solvers, problems, proof.getServices());

        reporter.phase(TGPhase.FINISHED);
        reporter.finish();
    }
}
