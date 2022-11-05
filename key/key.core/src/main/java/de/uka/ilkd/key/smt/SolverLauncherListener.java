package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.smt.solvertypes.SolverType;

import java.util.Collection;

/**
 * This interface can be used to observe a launcher.
 */
public interface SolverLauncherListener {

    public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers);

    public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes,
            SolverLauncher launcher);
}
