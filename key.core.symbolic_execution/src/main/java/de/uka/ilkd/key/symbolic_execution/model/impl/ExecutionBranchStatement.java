/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Switch;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionBranchStatement}.
 *
 * @author Martin Hentschel
 */
public class ExecutionBranchStatement extends AbstractExecutionBlockStartNode<BranchStatement>
        implements IExecutionBranchStatement {
    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     */
    public ExecutionBranchStatement(ITreeSettings settings, Node proofNode) {
        super(settings, proofNode);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() {
        BranchStatement bs = getActiveStatement();
        if (bs instanceof If) {
            PrettyPrinter p = PrettyPrinter.purePrinter();
            p.performActionOnIf((If) bs, false);
            return p.result();
        } else if (bs instanceof Switch) {
            PrettyPrinter p = PrettyPrinter.purePrinter();
            p.performActionOnSwitch((Switch) bs, false);
            return p.result();
        } else {
            return bs.toString();
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
        return "Branch Statement";
    }
}
