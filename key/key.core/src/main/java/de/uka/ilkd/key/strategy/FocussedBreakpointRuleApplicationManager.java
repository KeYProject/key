// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy;

import java.util.Optional;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;

/**
 * A rule app manager that ensures that rules are only applied to a certain
 * subterm within the proof (within a goal). The real work is delegated to a
 * second manager (delegate pattern), this class only filters rule applications
 */
public class FocussedBreakpointRuleApplicationManager
        implements DelegationBasedAutomatedRuleApplicationManager {

    private final AutomatedRuleApplicationManager delegate;
    private final Optional<String> breakpoint;

    private FocussedBreakpointRuleApplicationManager(
            AutomatedRuleApplicationManager delegate,
            Optional<String> breakpoint) {
        this.delegate = delegate;
        this.breakpoint = breakpoint;
    }

    public FocussedBreakpointRuleApplicationManager(
            AutomatedRuleApplicationManager delegate, Goal goal,
            Optional<PosInOccurrence> focussedSubterm,
            Optional<String> breakpoint) {
        this(focussedSubterm
                .map(pio -> new FocussedRuleApplicationManager(delegate, goal,
                        pio))
                .map(AutomatedRuleApplicationManager.class::cast)
                .orElse(delegate), breakpoint);

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
        return new FocussedBreakpointRuleApplicationManager(delegate.copy(),
                breakpoint);
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
    public void rulesAdded(ImmutableList<? extends RuleApp> rules,
            PosInOccurrence pos) {
        ImmutableList<RuleApp> applicableRules = //
                ImmutableSLList.<RuleApp> nil();
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

        if ((!(rule instanceof Taclet)
                || NodeInfo.isSymbolicExecution((Taclet) rule.rule()))
                && isJavaPIO(pos)) {
            final SourceElement activeStmt = //
                    JavaTools.getActiveStatement(pos.subTerm().javaBlock());
            final String currStmtString = activeStmt.toString();

            if (currStmtString != null && //
                    (currStmtString.contains("{")
                            ? currStmtString.substring(0,
                                    currStmtString.indexOf("{"))
                            : currStmtString).trim().equals(breakpoint.get())) {
                return false;
            }
        }

        return true;
    }

    private static boolean isJavaPIO(PosInOccurrence pio) {
        return pio != null
                && pio.subTerm().javaBlock() != JavaBlock.EMPTY_JAVABLOCK;
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
