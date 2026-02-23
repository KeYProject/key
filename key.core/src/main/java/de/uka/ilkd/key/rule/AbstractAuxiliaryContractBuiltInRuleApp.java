/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.AuxiliaryContract;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * Application for {@link AbstractAuxiliaryContractRule}.
 *
 * @author wacker, lanzinger
 */
public abstract class AbstractAuxiliaryContractBuiltInRuleApp<T extends BuiltInRule>
        extends AbstractBuiltInRuleApp<T> {

    /**
     * @see #getStatement()
     */
    private @Nullable JavaStatement statement;

    /**
     * @see #getHeapContext()
     *      FIXME weigl: should this not be {@link ImmutableList}?
     */
    protected @Nullable List<LocationVariable> heaps;


    /**
     * @see #getExecutionContext()
     */
    protected ExecutionContext context;

    /**
     *
     * @param rule the rule being applied.
     * @param occurrence the position at which the rule is applied.
     * @param ifInstantiations if instantiations.
     */
    protected AbstractAuxiliaryContractBuiltInRuleApp(T rule, PosInOccurrence occurrence,
            @Nullable ImmutableList<PosInOccurrence> ifInstantiations) {
        super(rule, occurrence, ifInstantiations);
    }

    /**
     *
     * @param s the statement (block or loop) which the applied contract belongs to.
     */
    public void setStatement(@Nullable JavaStatement s) {
        this.statement = s;
    }

    /**
     *
     * @return the statement (block or loop) which the applied contract belongs to.
     */
    public JavaStatement getStatement() {
        return statement;
    }

    /**
     *
     * @return the contract being applied.
     */
    public abstract AuxiliaryContract getContract();


    /**
     *
     * @return the execution context in which the block occurrs.
     */
    public ExecutionContext getExecutionContext() {
        return context;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return heaps;
    }

    @Override
    public boolean complete() {
        return pio != null && statement != null && getContract() != null && heaps != null;
    }

    @Override
    public boolean isSufficientlyComplete() {
        return pio != null;
    }

    /**
     * @param goal the current goal.
     * @return {@code true} iff the rule application cannot be completed for the current goal.
     */
    public boolean cannotComplete(final Goal goal) {
        return !builtInRule.isApplicable(goal, pio);
    }


}
