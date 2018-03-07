package de.uka.ilkd.key.rule;

import java.util.List;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.SimpleLoopContract;

/**
 * Application of {@link AbstractLoopContractRule}.
 */
public abstract class AbstractLoopContractBuiltInRuleApp
        extends AbstractBlockSpecificationElementBuiltInRuleApp {

    protected LoopContract contract;

    public AbstractLoopContractBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence occurrence,
            ImmutableList<PosInOccurrence> ifInstantiations) {
        super(rule, occurrence, ifInstantiations);
    }

    @Override
    public LoopContract getContract() {
        return contract;
    }

    public AbstractLoopContractBuiltInRuleApp tryToInstantiate(final Goal goal, final AbstractLoopContractRule rule) {
        if (complete() || cannotComplete(goal)) {
            return this;
        }
        final Services services = goal.proof().getServices();
        final AbstractLoopContractRule.Instantiation instantiation =
                rule.instantiate(posInOccurrence().subTerm(), goal, services);
        final ImmutableSet<LoopContract> contracts =
                AbstractLoopContractRule.getApplicableContracts(instantiation, goal, services);
        block = instantiation.block;
        ImmutableSet<LoopContract> cons = DefaultImmutableSet.<LoopContract>nil();
        for (LoopContract cont : contracts) {
            if (cont.getBlock().getStartPosition().getLine() == block.getStartPosition().getLine()) {
                cons = cons.add(cont);
            }
        }
        contract = SimpleLoopContract.combine(cons, services);
        heaps = HeapContext.getModHeaps(services, instantiation.isTransactional());
        return this;
    }

    public void update(final StatementBlock block, final LoopContract contract,
            final List<LocationVariable> heaps) {
        this.block = block;
        this.contract = contract;
        this.heaps = heaps;
    }
}
