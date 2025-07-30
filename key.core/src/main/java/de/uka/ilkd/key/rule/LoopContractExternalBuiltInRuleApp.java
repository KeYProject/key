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

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Application of {@link LoopContractExternalRule}.
 *
 * @author lanzinger
 */
@NullMarked
public class LoopContractExternalBuiltInRuleApp<T extends LoopContractExternalRule>
        extends AbstractLoopContractBuiltInRuleApp<T> {

    /**
     *
     * @param rule the rule being applied.
     * @param occurrence the position at which the rule is applied.
     */
    public LoopContractExternalBuiltInRuleApp(final T rule,
            final PosInOccurrence occurrence) {
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
    public LoopContractExternalBuiltInRuleApp(final T rule,
            final PosInOccurrence occurrence,
            final @Nullable ImmutableList<PosInOccurrence> ifInstantiations,
            final @Nullable JavaStatement statement,
            final @Nullable LoopContract contract,
            final @Nullable List<LocationVariable> heaps) {
        super(rule, occurrence, ifInstantiations);
        assert rule != null;
        assert occurrence != null;
        setStatement(statement);
        this.contract = contract;
        this.heaps = heaps;
    }

    @Override
    public @NonNull LoopContractExternalBuiltInRuleApp<T> replacePos(
            final PosInOccurrence newOccurrence) {
        return new LoopContractExternalBuiltInRuleApp<>(builtInRule, newOccurrence, ifInsts,
            getStatement(), contract, heaps);
    }

    @Override
    public @NonNull LoopContractExternalBuiltInRuleApp<T> setAssumesInsts(
            final ImmutableList<PosInOccurrence> ifInstantiations) {
        setMutable(ifInstantiations);
        return this;
    }

    @Override
    public LoopContractExternalBuiltInRuleApp<T> tryToInstantiate(final Goal goal) {
        return (LoopContractExternalBuiltInRuleApp<T>) super.tryToInstantiate(goal,
            LoopContractExternalRule.INSTANCE);
    }
}
