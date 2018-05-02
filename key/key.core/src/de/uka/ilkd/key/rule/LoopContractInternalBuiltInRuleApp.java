package de.uka.ilkd.key.rule;

import java.util.List;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopContract;

/**
 * Application of {@link LoopContractInternalRule}.
 */
public class LoopContractInternalBuiltInRuleApp extends AbstractLoopContractBuiltInRuleApp {

    public LoopContractInternalBuiltInRuleApp(final BuiltInRule rule,
            final PosInOccurrence occurrence) {
        this(rule, occurrence, null, null, null, null);
    }

    public LoopContractInternalBuiltInRuleApp(final BuiltInRule rule,
                                       final PosInOccurrence occurrence,
                                       final ImmutableList<PosInOccurrence> ifInstantiations,
                                       final StatementBlock block,
                                       final LoopContract contract,
                                       final List<LocationVariable> heaps) {
        super(rule, occurrence, ifInstantiations);
        assert rule != null;
        assert rule instanceof LoopContractInternalRule;
        assert occurrence != null;
        this.block = block;
        this.contract = contract;
        this.heaps = heaps;
    }

    @Override
    public LoopContractInternalBuiltInRuleApp replacePos(final PosInOccurrence newOccurrence) {
        return new LoopContractInternalBuiltInRuleApp(
                builtInRule, newOccurrence, ifInsts, block, contract, heaps);
    }

    @Override
    public LoopContractInternalBuiltInRuleApp setIfInsts(
            final ImmutableList<PosInOccurrence> ifInstantiations) {
        setMutable(ifInstantiations);
        return this;
    }

    @Override
    public LoopContractInternalBuiltInRuleApp tryToInstantiate(final Goal goal) {

        return (LoopContractInternalBuiltInRuleApp)
                super.tryToInstantiate(goal, LoopContractInternalRule.INSTANCE);
    }
}
