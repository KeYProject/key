/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.Set;

import de.uka.ilkd.key.prover.StopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint;

/**
 * Defines the basic functionality of an {@link StopCondition} which stops applying rules when at
 * least one {@link IBreakpoint} is hit.
 *
 * @author Martin Hentschel
 */
public interface IBreakpointStopCondition extends StopCondition {
    /**
     * Adds a new {@link IBreakpoint}.
     *
     * @param breakpoint The {@link IBreakpoint} to add.
     */
    void addBreakpoint(IBreakpoint breakpoint);

    /**
     * Removes an {@link IBreakpoint}.
     *
     * @param breakpoint The {@link IBreakpoint} to remove.
     */
    void removeBreakpoint(IBreakpoint breakpoint);

    /**
     * Returns all available {@link IBreakpoint}s.
     *
     * @return The available {@link IBreakpoint}s.
     */
    Set<IBreakpoint> getBreakpoints();
}
