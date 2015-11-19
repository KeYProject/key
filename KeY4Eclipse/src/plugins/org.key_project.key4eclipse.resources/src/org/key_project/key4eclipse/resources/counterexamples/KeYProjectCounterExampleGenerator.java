package org.key_project.key4eclipse.resources.counterexamples;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.gui.smt.SolverListener.InternSMTProblem;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.counterexample.AbstractSideProofCounterExampleGenerator;
import de.uka.ilkd.key.smt.model.Model;

public class KeYProjectCounterExampleGenerator extends AbstractSideProofCounterExampleGenerator {

    private final List<InternSMTProblem> problems = new LinkedList<InternSMTProblem>();
    
    private final List<KeYProjectCounterExample> keYProjectCounterExamples = new LinkedList<KeYProjectCounterExample>();
    
    public List<KeYProjectCounterExample> getKeYProjectCounterExamples(){
        return keYProjectCounterExamples;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected SolverLauncherListener createSolverListener(SMTSettings settings, Proof proof) {
       return new SolverLauncherListener() {
          @Override
          public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes, SolverLauncher launcher) {
             handleLauncherStarted(problems, solverTypes, launcher);
          }
          
          @Override
          public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {
             handleLauncherStopped(launcher, finishedSolvers);
          }
       };
    }

    /**
     * When the {@link SolverLauncher} is started.
     * @param smtproblems The {@link SMTProblem}s.
     * @param solverTypes The {@link SolverType}s.
     * @param launcher The started {@link SolverLauncher}.
     */
    protected void handleLauncherStarted(Collection<SMTProblem> smtproblems, 
                                         Collection<SolverType> solverTypes, 
                                         SolverLauncher launcher) {
       // Create InternSMTProblem
       int x = 0;
       int y=0;
       for (SMTProblem problem : smtproblems) {
          y = 0;
          for (SMTSolver solver : problem.getSolvers()) {
             problems.add(new InternSMTProblem(x, y, problem, solver));
             y++;
          }
          x++;
       }
    }

    /**
     * When the {@link SolverLauncher} has been stopped.
     * @param launcher The stopped {@link SolverLauncher}.
     * @param finishedSolvers The finished {@link SMTSolver}.
     */
    protected void handleLauncherStopped(final SolverLauncher launcher, 
                                         final Collection<SMTSolver> finishedSolvers) {
        for (InternSMTProblem problem : problems) {
            if (problem.getSolver().getType() == SolverType.Z3_CE_SOLVER &&
                    problem.getSolver().getSocket().getQuery() != null) {
                Model model = problem.getSolver().getSocket().getQuery().getModel();
                model.removeUnnecessaryObjects();
                model.addAliases();
                keYProjectCounterExamples.add(new KeYProjectCounterExample(computeProblemId(problem), computeProblemName(problem), model));
            }
        }
    }

    /**
     * Computes the name of the given {@link InternSMTProblem}.
     * @param problem The {@link InternSMTProblem} to compute its name.
     * @return The computed name.
     */
    public static String computeProblemName(InternSMTProblem problem) {
       return problem.getProblem().getName() + " (" + problem.getSolver().getType().getName() + ")";
    }
    
    /**
     * Computes the unique ID of the given {@link InternSMTProblem}.
     * @param problem The {@link InternSMTProblem} to compute ID for.
     * @return The computed ID.
     */
    public static String computeProblemId(InternSMTProblem problem) {
       return "problem" + problem.getProblemIndex() + ", " + problem.getSolverIndex();
    }
}
