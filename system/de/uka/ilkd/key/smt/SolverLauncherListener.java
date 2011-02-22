package de.uka.ilkd.key.smt;

import java.util.Collection;





public interface SolverLauncherListener extends SolverListener {
    public void launcherStopped();
    public void launcherStarted(Collection<SMTProblem> problems,Collection<SolverType> solverTypes, SolverLauncher launcher);
}
