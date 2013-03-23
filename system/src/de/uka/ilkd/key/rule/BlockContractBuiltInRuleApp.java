package de.uka.ilkd.key.rule;

import java.util.*;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.Triple;

public class BlockContractBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private StatementBlock block;
    private BlockContract contract;
    private List<LocationVariable> heaps;
    private IFProofObligationVars infFlowVars;
    private ExecutionContext context;

    public BlockContractBuiltInRuleApp(final BuiltInRule rule, final PosInOccurrence occurrence) {
        this(rule, occurrence, null, null, null, null);
    }

    public BlockContractBuiltInRuleApp(final BuiltInRule rule,
                                       final PosInOccurrence occurrence,
                                       final ImmutableList<PosInOccurrence> ifInstantiations,
                                       final StatementBlock block,
                                       final BlockContract contract,
                                       final List<LocationVariable> heaps) {
        super(rule, occurrence, ifInstantiations);
        assert rule != null;
        assert rule instanceof BlockContractRule;
        assert occurrence != null;
        this.block = block;
        this.contract = contract;
        this.heaps = heaps;
    }

    public StatementBlock getBlock() {
        return block;
    }

    public BlockContract getContract() {
        return contract;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return heaps;
    }

    @Override
    public BlockContractBuiltInRuleApp replacePos(final PosInOccurrence newOccurrence) {
        return new BlockContractBuiltInRuleApp(builtInRule, newOccurrence, ifInsts,
                block, contract, heaps);
    }

    @Override
    public BlockContractBuiltInRuleApp setIfInsts(
            final ImmutableList<PosInOccurrence> ifInstantiations) {
        setMutable(ifInstantiations);
        return this;
    }

    @Override
    public boolean complete() {
        return pio != null && block != null && contract != null && heaps != null;
    }

    @Override
    public boolean isSufficientlyComplete() {
        return pio != null;
    }

    @Override
    public BlockContractBuiltInRuleApp tryToInstantiate(final Goal goal) {
        if (complete() || cannotComplete(goal)) {
            return this;
        }
        final Services services = goal.proof().getServices();
        final BlockContractRule.Instantiation instantiation =
                BlockContractRule.instantiate(posInOccurrence().subTerm(), goal, services);
        final ImmutableSet<BlockContract> contracts =
                BlockContractRule.getApplicableContracts(instantiation, goal, services);
        block = instantiation.block;
        ImmutableSet<BlockContract> cons = DefaultImmutableSet.<BlockContract>nil();
        for (BlockContract cont : contracts) {
            if (cont.getBlock().getStartPosition().getLine() == block.getStartPosition().getLine()) {
                cons = cons.add(cont);
            }
        }
        contract = SimpleBlockContract.combine(cons, services);
        heaps = HeapContext.getModHeaps(services, instantiation.isTransactional());
        return this;
    }

    public boolean cannotComplete(final Goal goal) {
        return !builtInRule.isApplicable(goal, pio);
    }

    public void update(final StatementBlock block, final BlockContract contract,
                       final List<LocationVariable> heaps) {
        this.block = block;
        this.contract = contract;
        this.heaps = heaps;
    }

    public void update(IFProofObligationVars vars, ExecutionContext context) {
        this.infFlowVars = vars;
        this.context = context;
    }

    public IFProofObligationVars getInformationFlowProofObligationVars() {
        return infFlowVars;
    }

    public ExecutionContext getExecutionContext() {
        return context;
    }

    /*ImmutableSet<BlockContract> filterContracts(ImmutableSet<BlockContract> ifContracts,
                                                StatementBlock block) {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.<BlockContract>nil();
        for (BlockContract cont : ifContracts) {
            if ((cont.getBlock().getStartPosition().getLine() ==
                    block.getStartPosition().getLine())) {
                result = result.add(cont);
            }
        }
        return result;
    }*/
}