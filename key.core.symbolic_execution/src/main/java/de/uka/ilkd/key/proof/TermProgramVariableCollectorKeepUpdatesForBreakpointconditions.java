/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.strategy.IBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.AbstractConditionalBreakpoint;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint;

public class TermProgramVariableCollectorKeepUpdatesForBreakpointconditions
        extends TermProgramVariableCollector {
    private final IBreakpointStopCondition breakpointStopCondition;

    public TermProgramVariableCollectorKeepUpdatesForBreakpointconditions(Services services,
            IBreakpointStopCondition breakpointStopCondition) {
        super(services);
        this.breakpointStopCondition = breakpointStopCondition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void visit(Term t) {
        super.visit(t);
        if (t.op() instanceof Modality) {
            addVarsToKeep();
        }
    }

    private void addVarsToKeep() {
        for (IBreakpoint breakpoint : breakpointStopCondition.getBreakpoints()) {
            if (breakpoint instanceof AbstractConditionalBreakpoint) {
                AbstractConditionalBreakpoint conditionalBreakpoint =
                    (AbstractConditionalBreakpoint) breakpoint;
                if (conditionalBreakpoint.getToKeep() != null) {
                    for (LocationVariable sub : conditionalBreakpoint.getToKeep()) {
                        if (sub instanceof LocationVariable) {
                            super.result().add(sub);
                        }
                    }
                }
            }
        }
    }
}
