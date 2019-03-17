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
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.SimpleBlockContract;

/**
 * Application of {@link AbstractBlockContractRule}.
 *
 * @author wacker, lanzinger
 */
public abstract class AbstractBlockContractBuiltInRuleApp
        extends AbstractBlockSpecificationElementBuiltInRuleApp {

    /**
     * @see #getContract()
     */
    protected BlockContract contract;

    /**
     *
     * @param rule
     *            the rule being applied.
     * @param occurrence
     *            the position at which the rule is applied.
     * @param ifInstantiations
     *            if instantiations.
     */
    public AbstractBlockContractBuiltInRuleApp(BuiltInRule rule, PosInOccurrence occurrence,
            ImmutableList<PosInOccurrence> ifInstantiations) {
        super(rule, occurrence, ifInstantiations);
    }

    @Override
    public BlockContract getContract() {
        return contract;
    }

    /**
     *
     * @param goal
     *            the current goal.
     * @param rule
     *            the rule being applied.
     * @return this.
     */
    public AbstractBlockContractBuiltInRuleApp tryToInstantiate(final Goal goal,
            final AbstractBlockContractRule rule) {
        if (complete() || cannotComplete(goal)) {
            return this;
        }
        final Services services = goal.proof().getServices();
        final AbstractBlockContractRule.Instantiation instantiation = rule
                .instantiate(posInOccurrence().subTerm(), goal, services);
        final ImmutableSet<BlockContract> contracts = AbstractBlockContractRule
                .getApplicableContracts(instantiation, goal, services);
        block = instantiation.block;
        ImmutableSet<BlockContract> cons = DefaultImmutableSet.<BlockContract> nil();
        for (BlockContract cont : contracts) {
            if (cont.getBlock().getStartPosition().getLine() == block.getStartPosition()
                    .getLine()) {
                cons = cons.add(cont);
            }
        }
        contract = SimpleBlockContract.combine(cons, services);
        heaps = HeapContext.getModHeaps(services, instantiation.isTransactional());
        return this;
    }

    /**
     *
     * @param block
     *            the new block.
     * @param contract
     *            the new contract.
     * @param heaps
     *            the new heap context.
     */
    public void update(final StatementBlock block, final BlockContract contract,
            final List<LocationVariable> heaps) {
        this.block = block;
        this.contract = contract;
        this.heaps = heaps;
    }
}
