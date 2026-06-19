/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

/**
 * Listener for {@link IsabelleSolver}s.
 */
public interface IsabelleSolverListener {
    /**
     * Solver has started. Called after finishing preparations.
     *
     * @param solver the solver
     * @param problem the problem the solver is working on
     */
    void processStarted(IsabelleSolver solver, IsabelleProblem problem);

    /**
     * Solver has encountered an error.
     *
     * @param solver the solver
     * @param problem the problem the solver is working on
     * @param e the exception the solver encountered
     */
    void processError(IsabelleSolver solver, IsabelleProblem problem, Exception e);

    /**
     * Solver has stopped as planned
     *
     * @param solver the solver
     * @param problem the problem the solver is working on
     */
    void processStopped(IsabelleSolver solver, IsabelleProblem problem);
}
