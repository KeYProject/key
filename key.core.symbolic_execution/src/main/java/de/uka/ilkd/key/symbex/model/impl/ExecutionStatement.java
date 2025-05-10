/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbex.model.impl;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbex.model.IExecutionConstraint;
import de.uka.ilkd.key.symbex.model.IExecutionNode;
import de.uka.ilkd.key.symbex.model.IExecutionStatement;
import de.uka.ilkd.key.symbex.model.ITreeSettings;
import de.uka.ilkd.key.symbex.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionStatement}.
 *
 * @author Martin Hentschel
 */
public class ExecutionStatement extends AbstractExecutionNode<SourceElement>
        implements IExecutionStatement {
    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     */
    public ExecutionStatement(ITreeSettings settings, Node proofNode) {
        super(settings, proofNode);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() {
        return getActiveStatement().toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected IExecutionConstraint[] lazyComputeConstraints() {
        return SymbolicExecutionUtil.createExecutionConstraints(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getElementType() {
        return "Statement";
    }
}
