package de.uka.ilkd.key.rule;

import java.util.*;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.*;

public class BlockContractBuiltInRuleApp extends AbstractContractRuleApp {

	private final StatementBlock block;
	private List<LocationVariable> heapContext;
	
	public BlockContractBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pos) {
        this(rule, pos, null, null);
    }

    protected BlockContractBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio, ImmutableList<PosInOccurrence> ifInsts,
            BlockContract contract) {
        super(rule, pio, ifInsts, contract);
        assert pio != null;
        //TODO JavaTools.getActiveBlock ist not correct. We rather want the first block that has an applicable contract.
        //     See BlockContractRule#computeInstantiation.
        this.block = contract != null ? contract.getBlock() : JavaTools.getActiveBlock(programTerm().javaBlock());
        assert block != null;
        //this.contract = contract; //instantiateIndexValues(contract);
        //this.heapContext = heapContext;
    }
    
    protected BlockContractBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio, BlockContract contract) {
        this(rule, pio, null, contract);
    }

    public BlockContract getContract() {
        return (BlockContract) instantiation;
    }

    public StatementBlock getBlock() {
        return block;
    }

    public Term programTerm() {
        if (posInOccurrence() != null) {
            return TermBuilder.DF.goBelowUpdates(posInOccurrence().subTerm());
        }
        return null;
    }
	
	@Override
	public BlockContractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
		return new BlockContractBuiltInRuleApp(builtInRule, newPos, ifInsts, getContract());
	}

	public ImmutableSet<BlockContract> retrieveBlockContractsFromSpecification(Services services) {
        return services.getSpecificationRepository().getBlockContracts(block);
    }

	@Override
	public BlockContractBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
		setMutable(ifInsts);
        return this;
	}
	
	/*public BlockContractBuiltInRuleApp setBlockContract(BlockContract contract) {
        return new BlockContractBuiltInRuleApp(builtInRule, pio, ifInsts, contract, heapContext);
    }*/

    @Override
    public BlockContractBuiltInRuleApp setContract(Contract contract) {
        assert contract instanceof BlockContract;
        return new BlockContractBuiltInRuleApp(rule(), posInOccurrence(), (BlockContract) contract);
    }

	@Override
	public BlockContractBuiltInRuleApp tryToInstantiate(Goal goal) {
        if (complete()) {
            return this;
        }
        Services services = goal.proof().getServices();
        ImmutableSet<BlockContract> contracts = BlockContractRule.getApplicableContracts(
                BlockContractRule.computeInstantiation(posInOccurrence().subTerm(), services), services);
        Modality m = (Modality) programTerm().op();
        boolean transaction = (m == Modality.DIA_TRANSACTION || m == Modality.BOX_TRANSACTION);
        heapContext = HeapContext.getModHeaps(goal.proof().getServices(), transaction);
        //TODO Make pretty.
        ImmutableSet<FunctionalOperationContract> fcs = DefaultImmutableSet.<FunctionalOperationContract>nil();
        for (BlockContract c : contracts) {
            fcs = fcs.add(c);
        }
        FunctionalOperationContractImpl combinedContract
                = (FunctionalOperationContractImpl) services.getSpecificationRepository().combineOperationContracts(fcs);
        /*Map<Label, Term> breaks = new HashMap<Label, Term>();
        Map<Label, Term> continues = new HashMap<Label, Term>();
        Term returns = TermBuilder.DF.tt();
        for (BlockContract c : contracts) {
            BlockContractImpl contract = (BlockContractImpl) c;
            Map<Label, Term> internalBreaks = contract.getInternalBreaks();
            for (Map.Entry<Label, Term> breac : internalBreaks.entrySet()) {
                Label label = breac.getKey();
                Term formula = breac.getValue();
                if (breaks.get(label) == null) {
                    breaks.put(label, formula);
                }
                else {
                    breaks.put(label, TermBuilder.DF.and(breaks.get(label), formula));
                }
            }
            Map<Label, Term> internalContinues = contract.getInternalContinues();
            for (Map.Entry<Label, Term> kontinue : internalContinues.entrySet()) {
                Label label = kontinue.getKey();
                Term formula = kontinue.getValue();
                if (continues.get(label) == null) {
                    continues.put(label, formula);
                }
                else {
                    continues.put(label, TermBuilder.DF.and(continues.get(label), formula));
                }
            }
            returns = TermBuilder.DF.and(returns, contract.getInternalReturns());
        }*/

        //sort contracts alphabetically (for determinism) (see combineOperationContracts)
        BlockContract[] contractsArray
                = contracts.toArray(new BlockContract[contracts.size()]);
        Arrays.sort(contractsArray, new Comparator<BlockContract>() {
            public int compare(BlockContract c1, BlockContract c2) {
                return c1.getName().compareTo(c2.getName());
            }
        });
        BlockContract firstContract = contractsArray[0];

        return setContract(combinedContract.toBlockContract(block, firstContract.getInternalBreakFlags(),
                firstContract.getInternalContinueFlags(), firstContract.getInternalReturnFlag()));
	}
	
	@Override
    public List<LocationVariable> getHeapContext() {
      return heapContext;
    }

}
