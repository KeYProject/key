/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionLoopStatement}.
 *
 * @author Martin Hentschel
 */
public class ExecutionLoopStatement extends AbstractExecutionBlockStartNode<LoopStatement>
        implements IExecutionLoopStatement {
    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     */
    public ExecutionLoopStatement(ITreeSettings settings, Node proofNode) {
        super(settings, proofNode);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() {
        LoopStatement ls = getActiveStatement();
        if (ls.getGuardExpression() != null) {
            if (ls instanceof While) {
                PrettyPrinter p = PrettyPrinter.purePrinter();
                p.performActionOnWhile((While) ls, false);
                return p.result();
            } else if (ls instanceof For) {
                PrettyPrinter p = PrettyPrinter.purePrinter();
                p.performActionOnFor((For) ls, false);
                return p.result();
            } else if (ls instanceof EnhancedFor) {
                PrettyPrinter p = PrettyPrinter.purePrinter();
                p.performActionOnEnhancedFor((EnhancedFor) ls, false);
                return p.result();
            } else if (ls instanceof Do) {
                PrettyPrinter p = PrettyPrinter.purePrinter();
                p.performActionOnDo((Do) ls, false);
                return p.result();
            } else {
                return ls.toString();
            }
        } else {
            return ls.toString();
        }
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
        return "Loop Statement";
    }
}
