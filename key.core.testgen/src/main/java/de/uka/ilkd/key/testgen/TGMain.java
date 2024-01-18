package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
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
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLog;
import de.uka.ilkd.key.testgen.template.Templates;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.List;

public class TGMain {
    public static void main(String[] args) throws ProblemLoaderException, InterruptedException {
        SolverTypes.Z3_CE_SOLVER.checkForSupport();

        var env = KeYEnvironment.load(new File(args[0]));
        TestGenerationLog log = new TestGenerationLog() {
            @Override
            public void writeln(String string) {
                System.out.println(string);
            }

            @Override
            public void write(String string) {
                System.out.print(string);
            }

            @Override
            public void writeException(Throwable t) {
                t.printStackTrace();
            }

            @Override
            public void testGenerationCompleted() {
                System.out.println("Completed!");
            }
        };

        Proof proof = env.getLoadedProof();
        final TestCaseGenerator tg = new TestCaseGenerator(proof, Templates.TEMPLATE_JUNIT4);
        tg.setLogger(log);


        NewSMTTranslationSettings newSettings = new NewSMTTranslationSettings();
        ProofDependentSMTSettings pdSettings = ProofDependentSMTSettings.getDefaultSettingsData();
        ProofIndependentSMTSettings piSettings = ProofIndependentSMTSettings.getDefaultSettingsData();
        final var smtSettings = new DefaultSMTSettings(pdSettings, piSettings, newSettings, proof);
        var launcher = new SolverLauncher(smtSettings);
        launcher.addListener(new SolverLauncherListener() {
            @Override
            public void launcherStopped(SolverLauncher launcher,
                                        Collection<SMTSolver> finishedSolvers) {
                try {
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
        var info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
        final ProverTaskListener ptl = env.getUi().getProofControl().getDefaultProverTaskListener();
        ptl.taskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro, macro.getName(), 0));
        info = macro.applyTo(env.getUi(), proof, proof.openEnabledGoals(), null, ptl);
        final Collection<SMTProblem> problems = SMTProblem.createSMTProblems(proof);
        launcher.launch(solvers, problems, proof.getServices());
    }
}
