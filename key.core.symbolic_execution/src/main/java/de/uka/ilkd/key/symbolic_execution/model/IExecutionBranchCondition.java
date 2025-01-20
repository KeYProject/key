/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionBranchCondition;

/**
 * <p>
 * A node in the symbolic execution tree which represents a branch condition, e.g. {@code x < 0}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionBranchCondition} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionBranchCondition
 */
public interface IExecutionBranchCondition extends IExecutionNode<SourceElement> {
    /**
     * Returns the optional additional branch label.
     *
     * @return The additional branch label if available or {@code null} if not available.
     */
    String getAdditionalBranchLabel();

    /**
     * Checks if the value of {@link #getBranchCondition()} is already computed.
     *
     * @return {@code true} value of {@link #getBranchCondition()} is already computed,
     *         {@code false} value of {@link #getBranchCondition()} needs to be computed.
     */
    boolean isBranchConditionComputed();

    /**
     * <p>
     * Returns the branch condition as {@link Term}.
     * </p>
     * <p>
     * If this branch conditions merged proof nodes this {@link Term} is the overall branch
     * condition.
     * </p>
     *
     * @return The branch condition as {@link Term}.
     */
    Term getBranchCondition() throws ProofInputException;

    /**
     * Returns the human readable branch condition as string.
     *
     * @return The human readable branch condition.
     */
    String getFormatedBranchCondition() throws ProofInputException;

    /**
     * Checks if this branch condition is a merged one.
     *
     * @return {@code true} is merged branch condition, {@code false} is normal branch condition.
     */
    boolean isMergedBranchCondition();

    /**
     * <p>
     * Returns the branch condition nodes in KeY's proof tree which are merged into this
     * {@link IExecutionBranchCondition}.
     * </p>
     * <p>
     * It includes also {@link #getProofNode()}.
     * </p>
     *
     * @return The merged proof nodes.
     */
    Node[] getMergedProofNodes();

    /**
     * Returns the branch condition {@link Term}s.
     *
     * @return The branch condition {@link Term}s.
     */
    Term[] getMergedBranchCondtions() throws ProofInputException;
}
