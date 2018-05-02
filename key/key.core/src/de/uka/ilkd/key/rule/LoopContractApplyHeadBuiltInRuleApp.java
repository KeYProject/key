package de.uka.ilkd.key.rule;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopContract;

/**
 * @see LoopContractApplyHeadRule
 */
public class LoopContractApplyHeadBuiltInRuleApp extends AbstractBuiltInRuleApp {

    protected LoopContractApplyHeadRule rule;
    protected ImmutableSet<LoopContract> contracts;
    protected AbstractLoopContractRule.Instantiation instantiation;

    public LoopContractApplyHeadBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio) {
        this(rule, pio, null);
    }

    public LoopContractApplyHeadBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio, ImmutableSet<LoopContract> contracts) {
        super(rule, pio);
        this.rule = (LoopContractApplyHeadRule) rule;
        this.contracts = contracts;
    }

    @Override
    public boolean complete() {
        return pio != null && contracts != null && !contracts.isEmpty() && instantiation != null;
    }

    public boolean cannotComplete(final Goal goal) {
        return !rule.isApplicable(goal, pio);
    }

    @Override
    public boolean isSufficientlyComplete() {
        return pio != null;
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new LoopContractApplyHeadBuiltInRuleApp(rule, newPos, contracts);
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        instantiation =
                new AbstractLoopContractRule.Instantiator(
                        pio.subTerm(), goal, goal.proof().getServices())
                .instantiate();

        Services services = goal.proof().getServices();

        contracts =
                AbstractLoopContractRule.getApplicableContracts(instantiation, goal, services);
        rule = LoopContractApplyHeadRule.INSTANCE;
        return this;
    }
}
