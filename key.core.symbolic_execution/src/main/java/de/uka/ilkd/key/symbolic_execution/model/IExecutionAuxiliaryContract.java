/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionAuxiliaryContract;

/**
 * <p>
 * A node in the symbolic execution tree which represents a use block/loop contract application.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionAuxiliaryContract} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionAuxiliaryContract
 */
public interface IExecutionAuxiliaryContract extends IExecutionNode<SourceElement> {
    /**
     * Returns the applied {@link AuxiliaryContract}.
     *
     * @return The applied {@link AuxiliaryContract}.
     */
    AuxiliaryContract getContract();

    /**
     * Returns the {@link StatementBlock} at which the {@link BlockContract} is applied.
     *
     * @return The {@link StatementBlock} at which the {@link BlockContract} is applied.
     */
    StatementBlock getBlock();

    /**
     * Checks if the precondition is complied.
     *
     * @return {@code true} precondition complied, {@code false} precondition not complied.
     */
    boolean isPreconditionComplied();
}
