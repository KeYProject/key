/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
