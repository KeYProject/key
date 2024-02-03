/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
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
import de.uka.ilkd.key.testgen.settings.TestGenerationSettings;
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLog;
import org.jspecify.annotations.Nullable;

import java.io.IOException;
import java.util.Collection;
import java.util.List;

public record TestgenFacade(TestGenerationSettings settings) {
    /**
     * @param env
     * @param proof
     * @param settings
     * @param log
     * @throws InterruptedException
     */
    public static void generateTestcases(KeYEnvironment<?> env, Proof proof,
                                         TestGenerationSettings settings,
                                         @Nullable TestGenerationLog log) throws InterruptedException {
        final TestCaseGenerator tg = new TestCaseGenerator(proof, settings, log);

        NewSMTTranslationSettings newSettings = new NewSMTTranslationSettings();
        ProofDependentSMTSettings pdSettings = ProofDependentSMTSettings.getDefaultSettingsData();
        ProofIndependentSMTSettings piSettings = ProofIndependentSMTSettings.getDefaultSettingsData();

        piSettings.setTimeout(10000);
        final var smtSettings = new DefaultSMTSettings(pdSettings, piSettings, newSettings, proof);

        var launcher = new SolverLauncher(smtSettings);
        launcher.addListener(new SolverLauncherListener() {
            @Override
            public void launcherStopped(SolverLauncher launcher,
                                        Collection<SMTSolver> finishedSolvers) {
                try {
                    var first = finishedSolvers.iterator().next();
                    if(first.getException()!=null) {
                        throw new RuntimeException("Exception during SMT", first.getException());
                    }

                    tg.generateJUnitTestSuite(finishedSolvers);
                    if (tg.isJunit()) {
                        log.writeln("Compile the generated files using a Java compiler.");
                    } else {
                        log.writeln("Compile and run the file with openjml!");
                    }
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }

            @Override
            public void launcherStarted(Collection<SMTProblem> problems,
                                        Collection<SolverType> solverTypes, SolverLauncher launcher) {
            }
        });

        var solvers = List.of(SolverTypes.Z3_CE_SOLVER);
        final SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
        final ProverTaskListener ptl = env.getUi().getProofControl().getDefaultProverTaskListener();
        macro.applyTo(env.getUi(), proof, proof.openEnabledGoals(), null, ptl);
        final Collection<SMTProblem> problems = SMTProblem.createSMTProblems(proof);
        launcher.launch(solvers, problems, proof.getServices());
    }
}
