/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

public interface SolverListener {
    void processStarted(SMTSolver solver, SMTProblem problem);

    void processInterrupted(SMTSolver solver, SMTProblem problem, Throwable e);

    void processStopped(SMTSolver solver, SMTProblem problem);

    void processTimeout(SMTSolver solver, SMTProblem problem);

    void processUser(SMTSolver solver, SMTProblem problem);
}
