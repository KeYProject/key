/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * The default implementation of {@link IExecutionLoopCondition}.
 *
 * @author Martin Hentschel
 */
public class ExecutionLoopCondition extends AbstractExecutionBlockStartNode<JavaStatement>
        implements IExecutionLoopCondition {
    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     */
    public ExecutionLoopCondition(ITreeSettings settings, Node proofNode) {
        super(settings, proofNode);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() {
        return getGuardExpression().toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable Expression getGuardExpression() {
        if (getActiveStatement() instanceof LoopStatement) {
            return ((LoopStatement) getActiveStatement()).getGuardExpression();
        } else if (getActiveStatement() instanceof If) {
            return ((If) getActiveStatement()).getExpression();
        } else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @NonNull PositionInfo getGuardExpressionPositionInfo() {
        return getGuardExpression().getPositionInfo();
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
        return "Loop Condition";
    }
}
