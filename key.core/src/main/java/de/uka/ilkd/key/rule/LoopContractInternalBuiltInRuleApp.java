/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopContract;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Application of {@link LoopContractInternalRule}.
 *
 * @author lanzinger
 */
@NullMarked
public class LoopContractInternalBuiltInRuleApp<T extends LoopContractInternalRule>
        extends AbstractLoopContractBuiltInRuleApp<T> {

    /**
     *
     * @param rule the rule being applied.
     * @param occurrence the position at which the rule is applied.
     */
    public LoopContractInternalBuiltInRuleApp(final T rule, final PosInOccurrence occurrence) {
        this(rule, occurrence, null, null, null, null);
    }

    /**
     *
     * @param rule the rule being applied.
     * @param occurrence the position at which the rule is applied.
     * @param ifInstantiations if instantiations.
     * @param statement the statement which the applied contract belongs to.
     * @param contract the contract being applied.
     * @param heaps the heap context.
     */
    public LoopContractInternalBuiltInRuleApp(final T rule,
            final PosInOccurrence occurrence,
            @Nullable final ImmutableList<PosInOccurrence> ifInstantiations,
            @Nullable final JavaStatement statement, final @Nullable LoopContract contract,
            @Nullable final List<LocationVariable> heaps) {
        super(rule, occurrence, ifInstantiations);
        assert rule != null;
        assert rule instanceof LoopContractInternalRule;
        assert occurrence != null;
        setStatement(statement);
        this.contract = contract;
        this.heaps = heaps;
    }

    @Override
    public LoopContractInternalBuiltInRuleApp<T> replacePos(final PosInOccurrence newOccurrence) {
        return new LoopContractInternalBuiltInRuleApp<>(builtInRule, newOccurrence, ifInsts,
            getStatement(), contract, heaps);
    }

    @Override
    public LoopContractInternalBuiltInRuleApp<T> setAssumesInsts(
            final ImmutableList<PosInOccurrence> ifInstantiations) {
        setMutable(ifInstantiations);
        return this;
    }

    @Override
    public LoopContractInternalBuiltInRuleApp<T> tryToInstantiate(final Goal goal) {

        return (LoopContractInternalBuiltInRuleApp<T>) super.tryToInstantiate(goal,
            LoopContractInternalRule.INSTANCE);
    }
}
