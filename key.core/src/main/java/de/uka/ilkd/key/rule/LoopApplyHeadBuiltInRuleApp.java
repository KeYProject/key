/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopContract;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Rule application for {@link LoopApplyHeadRule}.
 *
 * @author lanzinger
 */
public class LoopApplyHeadBuiltInRuleApp extends AbstractBuiltInRuleApp {

    /**
     * The rule being applied.
     */
    private LoopApplyHeadRule rule;

    /**
     * The loop contracts on which the rule is applied.
     */
    protected ImmutableSet<LoopContract> contracts;

    /**
     * The instantiation.
     */
    protected AbstractLoopContractRule.Instantiation instantiation;

    /**
     *
     * @param rule the rule being applied.
     * @param pio the position at which the rule is applied.
     */
    public LoopApplyHeadBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio) {
        this(rule, pio, null);
    }

    /**
     *
     * @param rule the rule being applied.
     * @param pio the position at which the rule is applied.
     * @param contracts the contracts on which the rule is applied.
     */
    public LoopApplyHeadBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio,
            ImmutableSet<LoopContract> contracts) {
        super(rule, pio);
        this.rule = (LoopApplyHeadRule) rule;
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
        return !rule.isApplicable(goal, pio);
    }

    @Override
    public boolean isSufficientlyComplete() {
        return pio != null;
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new LoopApplyHeadBuiltInRuleApp(rule, newPos, contracts);
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        instantiation = new AbstractLoopContractRule.Instantiator(pio.subTerm(), goal,
            goal.proof().getServices()).instantiate();

        Services services = goal.proof().getServices();

        contracts = AbstractLoopContractRule.getApplicableContracts(instantiation, goal, services);
        rule = LoopApplyHeadRule.INSTANCE;
        return this;
    }
}
