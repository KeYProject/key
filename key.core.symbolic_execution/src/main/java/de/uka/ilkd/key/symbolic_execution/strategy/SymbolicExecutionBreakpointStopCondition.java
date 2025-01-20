/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.IBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint;

/**
 * An {@link IBreakpointStopCondition} which can be used during symbolic execution.
 *
 * @author Martin Hentschel
 */
public class SymbolicExecutionBreakpointStopCondition extends
        ExecutedSymbolicExecutionTreeNodesStopCondition implements IBreakpointStopCondition {
    /**
     * The used {@link IBreakpoint}s.
     */
    private final Set<IBreakpoint> breakpoints = new HashSet<>();

    /**
     * Creates a new {@link SymbolicExecutionBreakpointStopCondition}.
     *
     * @param breakpoints The {@link IBreakpoint} to use.
     */
    public SymbolicExecutionBreakpointStopCondition(IBreakpoint... breakpoints) {
        super(Integer.MAX_VALUE);
        if (breakpoints != null) {
            Collections.addAll(this.breakpoints, breakpoints);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getMaximalWork(int maxApplications, long timeout, Proof proof) {
        setMaximalNumberOfSetNodesToExecutePerGoal(Integer.MAX_VALUE);
        return super.getMaximalWork(maxApplications, timeout, proof);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, Goal goal) {
        for (IBreakpoint breakpoint : breakpoints) {
            breakpoint.updateState(maxApplications, timeout, proof, startTime, countApplied, goal);
        }
        return super.isGoalAllowed(maxApplications, timeout, proof, startTime, countApplied, goal);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void handleNodeLimitNotExceeded(int maxApplications, long timeout, Proof proof,
            long startTime, int countApplied, Goal goal, Node node, RuleApp ruleApp,
            Integer executedNumberOfSetNodes) {
        super.handleNodeLimitNotExceeded(maxApplications, timeout, proof, startTime, countApplied,
            goal, node, ruleApp, executedNumberOfSetNodes);
        SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
        if (isBreakpointHit(activeStatement, ruleApp, proof, node)) {
            setMaximalNumberOfSetNodesToExecutePerGoal(executedNumberOfSetNodes);
        }
    }

    /**
     * Checks if a breakpoint is hit.
     *
     * @param activeStatement the activeStatement of the node
     * @param ruleApp the applied {@link RuleApp}
     * @param proof the current proof
     * @param node the current node
     * @return {@code true} at least one breakpoint is hit, {@code false} all breakpoints are not
     *         hit.
     */
    protected boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Proof proof,
            Node node) {
        boolean result = false;
        Iterator<IBreakpoint> iter = breakpoints.iterator();
        while (!result && iter.hasNext()) {
            IBreakpoint next = iter.next();
            result =
                next.isEnabled() && next.isBreakpointHit(activeStatement, ruleApp, proof, node);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void addBreakpoint(IBreakpoint breakpoint) {
        breakpoints.add(breakpoint);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removeBreakpoint(IBreakpoint breakpoint) {
        breakpoints.remove(breakpoint);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<IBreakpoint> getBreakpoints() {
        return breakpoints;
    }
}
