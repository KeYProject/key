/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopContract;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Rule application for {@link LoopApplyHeadRule}.
 *
 * @author lanzinger
 */
@NullMarked
public class LoopApplyHeadBuiltInRuleApp extends AbstractBuiltInRuleApp<LoopApplyHeadRule> {
    /**
     * The loop contracts on which the rule is applied.
     */
    protected @Nullable ImmutableSet<LoopContract> contracts;

    /**
     * The instantiation.
     */
    protected AbstractLoopContractRule.Instantiation instantiation;

    /**
     * @param rule the rule being applied.
     * @param pio the position at which the rule is applied.
     */
    public LoopApplyHeadBuiltInRuleApp(LoopApplyHeadRule rule, @Nullable PosInOccurrence pio) {
        this(rule, pio, null);
    }

    /**
     * @param rule the rule being applied.
     * @param pio the position at which the rule is applied.
     * @param contracts the contracts on which the rule is applied.
     */
    public LoopApplyHeadBuiltInRuleApp(LoopApplyHeadRule rule, @Nullable PosInOccurrence pio,
            @Nullable ImmutableSet<LoopContract> contracts) {
        super(rule, pio);
        this.contracts = contracts;
    }

    @Override
    public boolean complete() {
        return pio != null && contracts != null && !contracts.isEmpty() && instantiation != null;
    }

    /**
     * @param goal the current goal.
     * @return {@code true} iff the rule application cannot be completed for the current goal.
     */
    public boolean cannotComplete(final Goal goal) {
        return !rule().isApplicable(goal, pio);
    }

    @Override
    public boolean isSufficientlyComplete() {
        return pio != null;
    }

    @Override
    public LoopApplyHeadBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new LoopApplyHeadBuiltInRuleApp(rule(), newPos, contracts);
    }

    @Override
    public IBuiltInRuleApp setAssumesInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public LoopApplyHeadBuiltInRuleApp tryToInstantiate(Goal goal) {
        assert pio != null;
        Services services = goal.proof().getServices();

        // TODO: FOR REVIEW (weigl):
        // Here we plugin the static reference directly. LCIR comes now w/o InfFlow support.
        final var instance = LoopContractInternalRule.INSTANCE;
        instantiation =
            instance.new Instantiator((JTerm) pio.subTerm(), goal)
                    .instantiate();

        contracts = instance.getApplicableContracts(instantiation, goal, services);
        return this;
    }
}
