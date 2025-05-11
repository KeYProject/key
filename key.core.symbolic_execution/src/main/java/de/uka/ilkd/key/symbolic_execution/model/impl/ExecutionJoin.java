/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionJoin;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.jspecify.annotations.NonNull;

/**
 * The default implementation of {@link IExecutionJoin}.
 *
 * @author Martin Hentschel
 */
public class ExecutionJoin extends AbstractExecutionNode<SourceElement> implements IExecutionJoin {
    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     */
    public ExecutionJoin(@NonNull ITreeSettings settings, @NonNull Node proofNode) {
        super(settings, proofNode);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected @NonNull String lazyComputeName() {
        return "Join";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected IExecutionConstraint @NonNull [] lazyComputeConstraints() {
        return SymbolicExecutionUtil.createExecutionConstraints(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @NonNull String getElementType() {
        return "Join";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isWeakeningVerified() {
        if (isWeakeningVerificationSupported()) {
            return SymbolicExecutionUtil.lazyComputeIsMainBranchVerified(getProofNode().child(0));
        } else {
            return true;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isWeakeningVerificationSupported() {
        return SymbolicExecutionUtil.isWeakeningGoalEnabled(getProof());
    }
}
