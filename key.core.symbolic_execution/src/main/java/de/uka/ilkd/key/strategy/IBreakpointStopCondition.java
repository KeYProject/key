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
    public void addBreakpoint(IBreakpoint breakpoint);

    /**
     * Removes an {@link IBreakpoint}.
     *
     * @param breakpoint The {@link IBreakpoint} to remove.
     */
    public void removeBreakpoint(IBreakpoint breakpoint);

    /**
     * Returns all available {@link IBreakpoint}s.
     *
     * @return The available {@link IBreakpoint}s.
     */
    public Set<IBreakpoint> getBreakpoints();
}
