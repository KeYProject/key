package de.uka.ilkd.key.rule;

import java.util.List;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopContractImpl;

/**
 * Application of {@link AbstractLoopContractRule}.
 *
 * @author lanzinger
 */
public abstract class AbstractLoopContractBuiltInRuleApp
        extends AbstractAuxiliaryContractBuiltInRuleApp {

    /**
     * @see #getContract()
     */
    protected LoopContract contract;

    /**
     *
     * @param rule
     *            the rule being applied.
     * @param occurrence
     *            the position at which the rule is applied.
     * @param ifInstantiations
     *            if instantiations.
     */
    public AbstractLoopContractBuiltInRuleApp(BuiltInRule rule, PosInOccurrence occurrence,
            ImmutableList<PosInOccurrence> ifInstantiations) {
        super(rule, occurrence, ifInstantiations);
    }

    @Override
    public LoopContract getContract() {
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
    public AbstractLoopContractBuiltInRuleApp tryToInstantiate(final Goal goal,
            final AbstractLoopContractRule rule) {
        if (complete() || cannotComplete(goal)) {
            return this;
        }
        final Services services = goal.proof().getServices();
        final AbstractLoopContractRule.Instantiation instantiation = rule
                .instantiate(posInOccurrence().subTerm(), goal, services);
        final ImmutableSet<LoopContract> contracts = AbstractLoopContractRule
                .getApplicableContracts(instantiation, goal, services);
        setStatement(instantiation.statement);
        ImmutableSet<LoopContract> cons = DefaultImmutableSet.<LoopContract> nil();
        for (LoopContract cont : contracts) {
            if (cont.isOnBlock() &&
                    cont.getBlock().getStartPosition().getLine()
                        == getStatement().getStartPosition().getLine()) {
                cons = cons.add(cont);
            } else if (!cont.isOnBlock() &&
                    cont.getLoop().getStartPosition().getLine() == getStatement().getStartPosition()
                    .getLine()) {
                cons = cons.add(cont);
            }
        }
        contract = LoopContractImpl.combine(cons, services);
        heaps = HeapContext.getModHeaps(services, instantiation.isTransactional());
        return this;
    }

    /**
     *
     * @param statement
     *            the new statement.
     * @param contract
     *            the new contract.
     * @param heaps
     *            the new heap context.
     */
    public void update(final JavaStatement statement, final LoopContract contract,
            final List<LocationVariable> heaps) {
        setStatement(statement);
        this.contract = contract;
        this.heaps = heaps;
    }
}
