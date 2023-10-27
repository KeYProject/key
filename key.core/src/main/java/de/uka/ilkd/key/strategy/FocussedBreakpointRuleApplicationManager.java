/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.Optional;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * A rule app manager that ensures that rules are only applied to a certain subterm within the proof
 * (within a goal). The real work is delegated to a second manager (delegate pattern), this class
 * only filters rule applications
 */
public class FocussedBreakpointRuleApplicationManager
        implements DelegationBasedAutomatedRuleApplicationManager {

    private final AutomatedRuleApplicationManager delegate;
    private final Optional<String> breakpoint;

    private FocussedBreakpointRuleApplicationManager(AutomatedRuleApplicationManager delegate,
            Optional<String> breakpoint) {
        this.delegate = delegate;
        this.breakpoint = breakpoint;
    }

    public FocussedBreakpointRuleApplicationManager(AutomatedRuleApplicationManager delegate,
            Goal goal, Optional<PosInOccurrence> focussedSubterm, Optional<String> breakpoint) {
        this(focussedSubterm.map(pio -> new FocussedRuleApplicationManager(delegate, goal, pio))
                .map(AutomatedRuleApplicationManager.class::cast).orElse(delegate),
            breakpoint);

        clearCache();
    }

    @Override
    public void clearCache() {
        delegate.clearCache();
    }

    @Override
    public AutomatedRuleApplicationManager copy() {
        return (AutomatedRuleApplicationManager) clone();
    }

    @Override
    public Object clone() {
        return new FocussedBreakpointRuleApplicationManager(delegate.copy(), breakpoint);
    }

    @Override
    public RuleApp peekNext() {
        return delegate.peekNext();
    }

    @Override
    public RuleApp next() {
        final RuleApp app = delegate.next();
        return app;
    }

    @Override
    public void setGoal(Goal p_goal) {
        delegate.setGoal(p_goal);
    }

    @Override
    public void ruleAdded(RuleApp rule, PosInOccurrence pos) {
        if (mayAddRule(rule, pos)) {
            delegate.ruleAdded(rule, pos);
        }
    }

    @Override
    public void rulesAdded(ImmutableList<? extends RuleApp> rules, PosInOccurrence pos) {
        ImmutableList<RuleApp> applicableRules = //
            ImmutableSLList.nil();
        for (RuleApp r : rules) {
            if (mayAddRule(r, pos)) {
                applicableRules = applicableRules.prepend(r);
            }
        }

        delegate.rulesAdded(applicableRules, pos);
    }

    private boolean mayAddRule(RuleApp rule, PosInOccurrence pos) {
        if (!breakpoint.isPresent()) {
            return true;
        }

        if ((!(rule instanceof Taclet) || NodeInfo.isSymbolicExecution((Taclet) rule.rule()))
                && isJavaPIO(pos)) {
            final SourceElement activeStmt = //
                JavaTools.getActiveStatement(pos.subTerm().javaBlock());
            final String currStmtString = activeStmt.toString();

            return currStmtString == null || //
                    !(currStmtString.contains("{")
                            ? currStmtString.substring(0, currStmtString.indexOf('{'))
                            : currStmtString).trim().equals(breakpoint.get());
        }

        return true;
    }

    private static boolean isJavaPIO(PosInOccurrence pio) {
        return pio != null && pio.subTerm().javaBlock() != JavaBlock.EMPTY_JAVABLOCK;
    }

    @Override
    public AutomatedRuleApplicationManager getDelegate() {
        if (delegate instanceof FocussedRuleApplicationManager) {
            return ((FocussedRuleApplicationManager) delegate).getDelegate();
        } else {
            return delegate;
        }
    }
}
