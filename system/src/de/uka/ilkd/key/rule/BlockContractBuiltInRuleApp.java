package de.uka.ilkd.key.rule;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.*;

public class BlockContractBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private StatementBlock block;
    private BlockContract contract;
    private List<LocationVariable> heaps;
	
	public BlockContractBuiltInRuleApp(final BuiltInRule rule, final PosInOccurrence occurrence)
    {
        this(rule, occurrence, null, null, null, null);
    }

    public BlockContractBuiltInRuleApp(final BuiltInRule rule,
                                       final PosInOccurrence occurrence,
                                       final ImmutableList<PosInOccurrence> ifInstantiations,
                                       final StatementBlock block,
                                       final BlockContract contract,
                                       final List<LocationVariable> heaps)
    {
        super(rule, occurrence, ifInstantiations);
        assert rule != null;
        assert rule instanceof BlockContractRule;
        assert occurrence != null;
        this.block = block;
        this.contract = contract;
        this.heaps = heaps;
    }

    public StatementBlock getBlock()
    {
        return block;
    }

    public BlockContract getContract()
    {
        return contract;
    }

    @Override
    public List<LocationVariable> getHeapContext()
    {
        return heaps;
    }
	
	@Override
	public BlockContractBuiltInRuleApp replacePos(final PosInOccurrence newOccurrence)
    {
		return new BlockContractBuiltInRuleApp(builtInRule, newOccurrence, ifInsts, block, contract, heaps);
	}

	@Override
	public BlockContractBuiltInRuleApp setIfInsts(final ImmutableList<PosInOccurrence> ifInstantiations)
    {
		setMutable(ifInstantiations);
        return this;
	}

    @Override
    public boolean complete()
    {
        return pio != null && block != null && contract != null && heaps != null;
    }

    @Override
    public boolean isSufficientlyComplete()
    {
        return pio != null;
    }

	@Override
	public BlockContractBuiltInRuleApp tryToInstantiate(final Goal goal)
    {
        if (complete() || cannotComplete(goal)) {
            return this;
        }
        // TODO Instead of static methods we could use non-static methods on builtInRule.
        final Services services = goal.proof().getServices();
        final BlockContractRule.Instantiation instantiation = BlockContractRule.instantiate(posInOccurrence().subTerm(), services);
        final ImmutableSet<BlockContract> contracts = BlockContractRule.getApplicableContracts(instantiation, services);
        final BlockContract contract = SimpleBlockContract.combine(contracts, services);
        final List<LocationVariable> heaps = HeapContext.getModHeaps(services, instantiation.transaction());
        return new BlockContractBuiltInRuleApp(builtInRule, pio, ifInsts, instantiation.block, contract, heaps);
	}

    private boolean cannotComplete(final Goal goal)
    {
        return !builtInRule.isApplicable(goal, pio);
    }

}