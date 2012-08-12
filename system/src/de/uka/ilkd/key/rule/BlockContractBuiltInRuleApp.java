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

    private BlockContract contract;
    private StatementBlock block;
	private List<LocationVariable> heaps;
	
	public BlockContractBuiltInRuleApp(final BuiltInRule rule, final PosInOccurrence occurrence)
    {
        this(rule, occurrence, null, null, null, null);
    }

    protected BlockContractBuiltInRuleApp(final BuiltInRule rule,
                                          final PosInOccurrence occurrence,
                                          final ImmutableList<PosInOccurrence> ifInstantiations,
                                          final BlockContract contract,
                                          final StatementBlock block,
                                          final List<LocationVariable> heaps)
    {
        super(rule, occurrence, ifInstantiations);
        assert occurrence != null;
        this.contract = contract;
        this.block = block;
        this.heaps = heaps;
    }

    public BlockContract getContract()
    {
        return contract;
    }

    // TODO Clean up.
    public BlockContractBuiltInRuleApp setContract(final BlockContract contract, final Goal goal)
    {
        this.block = contract.getBlock();
        this.contract = contract;
        if (heaps == null) {
            heaps = HeapContext.getModHeaps(goal.proof().getServices(), contract.getTransaction());
        }
        return this;
    }

    public StatementBlock getBlock()
    {
        return block;
    }

    @Override
    public List<LocationVariable> getHeapContext()
    {
        return heaps;
    }
	
	@Override
	public BlockContractBuiltInRuleApp replacePos(final PosInOccurrence newOccurrence)
    {
		return new BlockContractBuiltInRuleApp(builtInRule, newOccurrence, ifInsts, contract, block, heaps);
	}

	@Override
	public BlockContractBuiltInRuleApp setIfInsts(final ImmutableList<PosInOccurrence> ifInstantiations)
    {
		setMutable(ifInstantiations);
        return this;
	}

    //TODO Are the implementations of complete and isSufficientlyComplete correct?
    @Override
    public boolean complete()
    {
        return contract != null && block != null;
    }

    @Override
    public boolean isSufficientlyComplete()
    {
        return pio != null && block != null;
    }

	@Override
	public BlockContractBuiltInRuleApp tryToInstantiate(final Goal goal)
    {
        if (complete()) {
            return this;
        }
        //TODO Clean up.
        //TODO Check whether isApplicable is true first?
        final Services services = goal.proof().getServices();
        final BlockContractRule.Instantiation instantiation = BlockContractRule.instantiate(posInOccurrence().subTerm(), services);
        final ImmutableSet<BlockContract> contracts = BlockContractRule.getApplicableContracts(instantiation, services);
        final List<LocationVariable> heaps = HeapContext.getModHeaps(services, instantiation.modality.transaction());
        final BlockContract contract = SimpleBlockContract.combine(contracts, services);
        return new BlockContractBuiltInRuleApp(builtInRule, pio, ifInsts, contract, instantiation.block, heaps);
	}

}