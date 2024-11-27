/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import java.util.Objects;

import org.key_project.ncore.rules.RuleAbortException;
import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.proof.Goal;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.Nullable;

public abstract class AbstractBuiltInRuleApp implements IBuiltInRuleApp {
    protected final BuiltInRule builtInRule;

    protected final PosInOccurrence pio;
    protected ImmutableList<PosInOccurrence> ifInsts;

    protected AbstractBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts) {
        this.builtInRule = rule;
        this.pio = pio;
        this.ifInsts = (ifInsts == null ? ImmutableSLList.nil() : ifInsts);
    }

    protected AbstractBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio) {
        this(rule, pio, null);
    }

    /**
     * HACK: but strategies do not work otherwise at the moment; I need to have a closer look on
     * what is going on there This restores the behaviour as it was before my previous commit for
     * the moment
     */
    public void setMutable(ImmutableList<PosInOccurrence> ifInsts) {
        this.ifInsts = ifInsts;
    }

    /**
     * returns the rule of this rule application
     */
    @Override
    public BuiltInRule rule() {
        return builtInRule;
    }

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a position in the
     * corresponding formula) of this rule application
     */
    @Override
    public PosInOccurrence posInOccurrence() {
        return pio;
    }

    /**
     * applies the specified rule at the specified position if all schema variables have been
     * instantiated
     *
     * @param goal the Goal where to apply the rule
     * @return list of new created goals
     */
    @Override
    public @Nullable ImmutableList<Goal> execute(Goal goal) {
        goal.addAppliedRuleApp(this);
        try {
            return Objects.requireNonNull(builtInRule.apply(goal, this));
        } catch (RuleAbortException rae) {
            // goal.removeLastAppliedRuleApp();
            goal.getNode().setAppliedRuleApp(null);
            return null;
        }
    }

    public abstract AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos);

    @Override
    public abstract IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts);

    @Override
    public ImmutableList<PosInOccurrence> ifInsts() {
        return ifInsts;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.rule.IBuiltInRuleApp#tryToInstantiate(de.uka.ilkd.key.proof.Goal)
     */
    @Override
    public abstract AbstractBuiltInRuleApp tryToInstantiate(Goal goal);

    @Override
    public AbstractBuiltInRuleApp forceInstantiate(Goal goal) {
        return tryToInstantiate(goal);
    }

    /**
     * returns true if all variables are instantiated
     *
     * @return true if all variables are instantiated
     */
    @Override
    public boolean complete() {
        return true;
    }

    @Override
    public String toString() {
        return "BuiltInRule: " + rule().name() + " at pos " + pio.subTerm();
    }
}
