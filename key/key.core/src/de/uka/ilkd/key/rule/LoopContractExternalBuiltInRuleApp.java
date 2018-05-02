package de.uka.ilkd.key.rule;

import java.util.List;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopContract;

/**
 * Application of {@link LoopContractExternalRule}.
 */
public class LoopContractExternalBuiltInRuleApp
        extends AbstractLoopContractBuiltInRuleApp {

    public LoopContractExternalBuiltInRuleApp(final BuiltInRule rule,
            final PosInOccurrence occurrence) {
        this(rule, occurrence, null, null, null, null);
    }

    public LoopContractExternalBuiltInRuleApp(final BuiltInRule rule,
            final PosInOccurrence occurrence,
            final ImmutableList<PosInOccurrence> ifInstantiations,
            final StatementBlock block,
            final LoopContract contract,
            final List<LocationVariable> heaps) {
        super(rule, occurrence, ifInstantiations);
        assert rule != null;
        assert rule instanceof LoopContractExternalRule;
        assert occurrence != null;
        this.block = block;
        this.contract = contract;
        this.heaps = heaps;
    }

    @Override
    public LoopContractExternalBuiltInRuleApp replacePos(final PosInOccurrence newOccurrence) {
        return new LoopContractExternalBuiltInRuleApp(
                builtInRule, newOccurrence, ifInsts, block, contract, heaps);
    }

    @Override
    public LoopContractExternalBuiltInRuleApp setIfInsts(
            final ImmutableList<PosInOccurrence> ifInstantiations) {
        setMutable(ifInstantiations);
        return this;
    }

    @Override
    public LoopContractExternalBuiltInRuleApp tryToInstantiate(final Goal goal) {
        return (LoopContractExternalBuiltInRuleApp)
                super.tryToInstantiate(goal, LoopContractExternalRule.INSTANCE);
    }
}
