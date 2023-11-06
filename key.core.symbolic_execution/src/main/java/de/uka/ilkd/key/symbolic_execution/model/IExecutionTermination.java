/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionTermination;

/**
 * <p>
 * A node in the symbolic execution tree which represents the normal termination of a branch, e.g.
 * {@code <end>} in case of normal termination or {@code <uncaught java.lang.NullPointerException>}
 * in case of exceptional termination.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionTermination} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionTermination
 */
public interface IExecutionTermination extends IExecutionNode<SourceElement> {
    /**
     * The default name of a termination node with {@link TerminationKind#NORMAL}.
     */
    String NORMAL_TERMINATION_NODE_NAME =
        INTERNAL_NODE_NAME_START + "end" + INTERNAL_NODE_NAME_END;

    /**
     * The default name of a termination node with {@link TerminationKind#LOOP_BODY}.
     */
    String LOOP_BODY_TERMINATION_NODE_NAME =
        INTERNAL_NODE_NAME_START + "loop body end" + INTERNAL_NODE_NAME_END;

    /**
     * Returns the {@link IProgramVariable} which is used in the {@link Sequent} of
     * {@link Proof#root()} to check if a normal or exceptional termination occurred.
     *
     * @return The {@link IProgramVariable} which is used to caught global exceptions.
     */
    IProgramVariable getExceptionVariable();

    /**
     * Returns the {@link Sort} of the caught exception.
     *
     * @return The {@link Sort} of the caught exception.
     */
    Sort getExceptionSort();

    /**
     * Returns the {@link TerminationKind}.
     *
     * @return The {@link TerminationKind}.
     */
    TerminationKind getTerminationKind();

    /**
     * Checks if this branch would be closed without the uninterpreted predicate and thus be treated
     * as valid/closed in a regular proof.
     *
     * @return {@code true} verified/closed, {@code false} not verified/still open
     */
    boolean isBranchVerified();

    /**
     * Defines the possible termination kinds.
     *
     * @author Martin Hentschel
     */
    enum TerminationKind {
        /**
         * Normal termination without any exceptions.
         */
        NORMAL,

        /**
         * Termination with uncaught exception.
         */
        EXCEPTIONAL,

        /**
         * Partial termination of a loop body.
         */
        LOOP_BODY,

        /**
         * Normal termination without any exceptions of the block contract validity branch.
         */
        BLOCK_CONTRACT_NORMAL,

        /**
         * Termination with uncaught exception of the block contract validity branch.
         */
        BLOCK_CONTRACT_EXCEPTIONAL
    }
}
