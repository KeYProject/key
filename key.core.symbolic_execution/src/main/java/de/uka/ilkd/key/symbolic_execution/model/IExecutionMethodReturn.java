/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;

/**
 * <p>
 * A node in the symbolic execution tree which represents a method return, e.g. {@code return 42}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionMethodReturn} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionMethodReturn
 */
public interface IExecutionMethodReturn extends IExecutionBaseMethodReturn<SourceElement> {
    /**
     * Returns the human readable node name including the return value ({@link #getReturnValues()}).
     *
     * @return The human readable node name including the return value.
     * @throws ProofInputException Occurred Exception.
     */
    String getNameIncludingReturnValue() throws ProofInputException;

    /**
     * Returns the human readable signature including the return value ({@link #getReturnValues()}).
     *
     * @return The human readable signature including the return value.
     * @throws ProofInputException Occurred Exception.
     */
    String getSignatureIncludingReturnValue() throws ProofInputException;

    /**
     * Checks if the values of {@link #getReturnValues()} are already computed.
     *
     * @return {@code true} value of {@link #getReturnValues()} are already computed, {@code false}
     *         values of {@link #getReturnValues()} needs to be computed.
     */
    boolean isReturnValuesComputed();

    /**
     * Returns the possible return values.
     *
     * @return The possible return values.
     * @throws ProofInputException Occurred Exception.
     */
    IExecutionMethodReturnValue[] getReturnValues() throws ProofInputException;
}
