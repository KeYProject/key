/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.LoopContractInternalRule;
import de.uka.ilkd.key.rule.metaconstruct.EnhancedForElimination;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.ImmutableList;

/**
 * <p>
 * A contract for a block that begins with a loop.
 * </p>
 *
 * <p>
 * When a loop contract is encountered in an existing proof, a {@code LoopContract} is used. To
 * generate a new proof obligation for a block contract, use {@link FunctionalLoopContract} instead.
 * </p>
 *
 * @author lanzinger
 */
public interface LoopContract extends AuxiliaryContract {

    /**
     *
     * @return this loop contract's decreases clause.
     */
    Term getDecreases();

    /**
     *
     * @param heap the heap to use.
     * @param self the {@code self} variable to use instead of {@link #getPlaceholderVariables()}.
     * @param services services.
     * @return this loop contract's decreases clause on the specified heap.
     */
    Term getDecreases(Term heap, Term self, Services services);

    /**
     *
     * @param variables the variables to use instead of {@link #getPlaceholderVariables()}.
     * @param services services.
     * @return this loop contract's decreases clause.
     */
    Term getDecreases(Variables variables, Services services);

    /**
     * <p>
     * This contains any statements that are executed before the loop.
     * </p>
     *
     * <p>
     * It is only used if the loop is a for loop, in which case it contains the loop initializers
     * </p>
     *
     * @return statements to execute before the loop.
     */
    StatementBlock getHead();

    /**
     * @return the loop guard.
     */
    Expression getGuard();

    /**
     * @return the loop body.
     */
    StatementBlock getBody();

    /**
     * @return all statements after the loop.
     */
    StatementBlock getTail();

    /**
     * @return a loop of the form <code> while(&lt;getGuard()&gt;) { &lt;getBody()&gt; } </code>
     */
    LoopStatement getLoop();

    /**
     * @return all labels that belong to the loop, or an empty list if the loop is not a labeled
     *         statement.
     */
    List<Label> getLoopLabels();

    /**
     * @return {@code true} if this contract belongs to a block, {@code false} if it belongs to a
     *         loop.
     */
    boolean isOnBlock();

    /**
     *
     * @param newBlock the new block.
     * @param newPreconditions the new preconditions.
     * @param newPostconditions the new postconditions.
     * @param newModifiesClauses the new modifies clauses.
     * @param newFreeModifiesClauses the new free modifies clauses.
     * @param newinfFlowSpecs the new information flow specifications.
     * @param newVariables the new variables.
     * @param newMeasuredBy the new measured-by clause.
     * @param newDecreases the new decreases clause.
     * @return a new loop contract with the specified attributes.
     */
    LoopContract update(StatementBlock newBlock, Map<LocationVariable, Term> newPreconditions,
            Map<LocationVariable, Term> newFreePreconditions,
            Map<LocationVariable, Term> newPostconditions,
            Map<LocationVariable, Term> newFreePostconditions,
            Map<LocationVariable, Term> newModifiesClauses,
            Map<LocationVariable, Term> newFreeModifiesClauses,
            ImmutableList<InfFlowSpec> newinfFlowSpecs, Variables newVariables, Term newMeasuredBy,
            Term newDecreases);

    /**
     *
     * @param newLoop the new loop.
     * @param newPreconditions the new preconditions.
     * @param newPostconditions the new postconditions.
     * @param newModifiesClauses the new modifies clauses.
     * @param newFreeModifiesClauses the new free modifies clauses.
     * @param newinfFlowSpecs the new information flow specifications.
     * @param newVariables the new variables.
     * @param newMeasuredBy the new measured-by clause.
     * @param newDecreases the new decreases clause.
     * @return a new loop contract with the specified attributes.
     */
    LoopContract update(LoopStatement newLoop, Map<LocationVariable, Term> newPreconditions,
            Map<LocationVariable, Term> newFreePreconditions,
            Map<LocationVariable, Term> newPostconditions,
            Map<LocationVariable, Term> newFreePostconditions,
            Map<LocationVariable, Term> newModifiesClauses,
            Map<LocationVariable, Term> newFreeModifiesClauses,
            ImmutableList<InfFlowSpec> newinfFlowSpecs, Variables newVariables, Term newMeasuredBy,
            Term newDecreases);

    /**
     *
     * @return the index variable if {@link #getLoop()} is an enhanced for-loop, {@code null}
     *         otherwise.
     * @see EnhancedForElimination#getIndexVariable()
     */
    ProgramVariable getIndexVariable();

    /**
     *
     * @return the values variable if {@link #getLoop()} is an enhanced for-loop, {@code null}
     *         otherwise.
     * @see EnhancedForElimination#getValuesVariable()
     */
    ProgramVariable getValuesVariable();

    /**
     * @param newKJT the type containing the new target method.
     * @param newPM the new target method.
     * @return a new loop contract equal to this one except that it belongs to a different target.
     */
    @Override
    LoopContract setTarget(KeYJavaType newKJT, IObserverFunction newPM);

    /**
     * @param newBlock the new block.
     * @return a new loop contract equal to this one except that it belongs to a different block.
     */
    @Override
    LoopContract setBlock(StatementBlock newBlock);

    @Override
    LoopContract map(UnaryOperator<Term> op, Services services);

    /**
     * @param newLoop the new loop.
     * @return a new loop contract equal to this one except that it belongs to a different loop.
     */
    LoopContract setLoop(LoopStatement newLoop);

    /**
     * Replaces {@code \index} and {@code \values} with the proper variables in all terms of this
     * contract.
     *
     * @param newBlock a new block.
     * @param services services.
     * @return a new loop contract equal to this one except that it belongs to the new block, and
     *         {@code \index} and {@code \values} are replaced by proper variables in all terms.
     */
    LoopContract replaceEnhancedForVariables(StatementBlock newBlock, Services services);

    /**
     * @return {@code true} iff this contract should only be applied using
     *         {@link LoopContractInternalRule}.
     */
    boolean isInternalOnly();

    /**
     * Returns a {@code BlockContract} for {@link #getBlock()}.
     *
     * This is used to apply for-loop and for-each-loops: The block containing the loop is applied
     * using a block contract; inside that block contract's validity branch, the while-loop obtained
     * by transforming the for-loop is applied using a loop contract.
     *
     * @return a valid {@code BlockContract} for {@link #getBlock()}.
     */
    BlockContract toBlockContract();
}
