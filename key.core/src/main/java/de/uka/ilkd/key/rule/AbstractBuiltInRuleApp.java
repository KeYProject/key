/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;
import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


@NullMarked
public abstract class AbstractBuiltInRuleApp<T extends BuiltInRule> implements IBuiltInRuleApp {
    public static final AtomicLong PERF_EXECUTE = new AtomicLong();
    public static final AtomicLong PERF_SET_SEQUENT = new AtomicLong();

    protected final T builtInRule;

    protected final @Nullable PosInOccurrence pio;
    protected @Nullable ImmutableList<PosInOccurrence> ifInsts;

    protected AbstractBuiltInRuleApp(T rule, @Nullable PosInOccurrence pio,
            @Nullable ImmutableList<PosInOccurrence> ifInsts) {
        this.builtInRule = rule;
        this.pio = pio;
        this.ifInsts = (ifInsts == null ? ImmutableSLList.nil() : ifInsts);
    }

    protected AbstractBuiltInRuleApp(T rule, @Nullable PosInOccurrence pio) {
        this(rule, pio, null);
    }

    /**
     * HACK: but strategies do not work otherwise in the moment; I need to have a closer look on
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
    public T rule() {
        return builtInRule;
    }

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a position in the
     * corresponding formula) of this rule application
     */
    @Override
    public @Nullable PosInOccurrence posInOccurrence() {
        return pio;
    }

    /**
     * applies the specified rule at the specified position if all schema variables have been
     * instantiated
     */
    @Override
    public void checkApplicability() {
    }

    @Override
    public void registerSkolemConstants(Namespace<@NonNull Function> fns) {
    }

    public abstract AbstractBuiltInRuleApp<T> replacePos(PosInOccurrence newPos);

    @Override
    public abstract IBuiltInRuleApp setAssumesInsts(ImmutableList<PosInOccurrence> ifInsts);

    @Override
    public ImmutableList<PosInOccurrence> assumesInsts() {
        return ifInsts;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.rule.IBuiltInRuleApp#tryToInstantiate(de.uka.ilkd.key.proof.Goal)
     */
    @Override
    public abstract AbstractBuiltInRuleApp<T> tryToInstantiate(Goal goal);

    @Override
    public AbstractBuiltInRuleApp<T> forceInstantiate(Goal goal) {
        return tryToInstantiate(goal);
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.rule.IBuiltInRuleApp#isSufficientlyComplete()
     */
    @Override
    public boolean isSufficientlyComplete() {
        return complete();
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return null;
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
        return "BuiltInRule: %s at pos %s".formatted(rule().name(), pio.subTerm());
    }

}
