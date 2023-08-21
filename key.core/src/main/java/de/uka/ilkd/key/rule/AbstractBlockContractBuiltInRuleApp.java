/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockContractImpl;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Application of {@link AbstractBlockContractRule}.
 *
 * @author wacker, lanzinger
 */
public abstract class AbstractBlockContractBuiltInRuleApp
        extends AbstractAuxiliaryContractBuiltInRuleApp {

    /**
     * @see #getContract()
     */
    protected BlockContract contract;

    /**
     *
     * @param rule the rule being applied.
     * @param occurrence the position at which the rule is applied.
     * @param ifInstantiations if instantiations.
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
     * @param goal the current goal.
     * @param rule the rule being applied.
     * @return this.
     */
    public AbstractBlockContractBuiltInRuleApp tryToInstantiate(final Goal goal,
            final AbstractBlockContractRule rule) {
        if (complete() || cannotComplete(goal)) {
            return this;
        }
        final Services services = goal.proof().getServices();
        final AbstractBlockContractRule.Instantiation instantiation =
            rule.instantiate(posInOccurrence().subTerm(), goal, services);
        final ImmutableSet<BlockContract> contracts =
            AbstractBlockContractRule.getApplicableContracts(instantiation, goal, services);
        setStatement(instantiation.statement);
        ImmutableSet<BlockContract> cons = DefaultImmutableSet.nil();
        for (BlockContract cont : contracts) {
            if (cont.getBlock().getStartPosition().line() == getStatement().getStartPosition()
                    .line()) {
                cons = cons.add(cont);
            }
        }
        contract = BlockContractImpl.combine(cons, services);
        heaps = HeapContext.getModHeaps(services, instantiation.isTransactional());
        return this;
    }

    /**
     *
     * @param statement the new statement.
     * @param contract the new contract.
     * @param heaps the new heap context.
     */
    public void update(final JavaStatement statement, final BlockContract contract,
            final List<LocationVariable> heaps) {
        setStatement(statement);
        this.contract = contract;
        this.heaps = heaps;
    }
}
