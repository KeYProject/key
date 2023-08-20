/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Special {@link SymbolicLayoutExtractor} for {@link IExecutionNode}s.
 *
 * @author Martin Hentschel
 */
public class ExecutionNodeSymbolicLayoutExtractor extends SymbolicLayoutExtractor {
    /**
     * The {@link IExecutionNode} to extract memory layouts from.
     */
    private final IExecutionNode<?> executionNode;

    /**
     * Constructor.
     *
     * @param executionNode The {@link IExecutionNode} to extract memory layouts from.
     */
    public ExecutionNodeSymbolicLayoutExtractor(IExecutionNode<?> executionNode) {
        super(executionNode.getProofNode(), executionNode.getModalityPIO(),
            executionNode.getSettings().isUseUnicode(),
            executionNode.getSettings().isUsePrettyPrinting(),
            executionNode.getSettings().isSimplifyConditions());
        this.executionNode = executionNode;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String computeInitialStateName() {
        try {
            return SymbolicExecutionUtil.getRoot(executionNode).getName() + " resulting in "
                + computeCurrentStateName();
        } catch (ProofInputException e) {
            return e.getMessage();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String computeCurrentStateName() {
        try {
            return executionNode.getName();
        } catch (ProofInputException e) {
            return e.getMessage();
        }
    }
}
