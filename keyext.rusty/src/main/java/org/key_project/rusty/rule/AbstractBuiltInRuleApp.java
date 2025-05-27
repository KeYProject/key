/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;


import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.rusty.proof.Goal;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;


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

    public abstract AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos);

    @Override
    public abstract IBuiltInRuleApp setAssumesInsts(ImmutableList<PosInOccurrence> ifInsts);

    @Override
    public ImmutableList<PosInOccurrence> assumesInsts() {
        return ifInsts;
    }

    @Override
    public void checkApplicability() {

    }

    @Override
    public void registerSkolemConstants(Namespace<@NonNull Function> fns) {

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
