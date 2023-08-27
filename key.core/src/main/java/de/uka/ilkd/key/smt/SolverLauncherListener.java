/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.Collection;

import de.uka.ilkd.key.smt.solvertypes.SolverType;

/**
 * This interface can be used to observe a launcher.
 */
public interface SolverLauncherListener {

    void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers);

    void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes,
            SolverLauncher launcher);
}
