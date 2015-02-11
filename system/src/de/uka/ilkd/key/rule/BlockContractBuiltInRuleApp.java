// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.SimpleBlockContract;

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
        return new BlockContractBuiltInRuleApp(builtInRule, newOccurrence, ifInsts,block, contract, heaps);
    }

    @Override
    public BlockContractBuiltInRuleApp setIfInsts(final ImmutableList<PosInOccurrence> ifInstantiations) {
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
}