/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionVariable;

/**
 * <p>
 * A variable value pair contained in an {@link IExecutionNode}, e.g. the method parameter
 * {@code int x = 42;} will have the variable value pair {@code x = 42}. This class represents the
 * variable ({@code x}) which is represented while its values are represented as child
 * {@link IExecutionValue} instances.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionVariable} which is instantiated lazily by the
 * {@link IExecutionNode} implementations.
 * </p>
 *
 * @author Martin Hentschel
 * @see IExecutionNode
 * @see IExecutionValue
 * @see ExecutionVariable
 */
public interface IExecutionVariable extends IExecutionElement {
    /**
     * Returns the {@link IProgramVariable} which contains the represented value.
     *
     * @return The {@link IProgramVariable} which contains the represented value.
     */
    IProgramVariable getProgramVariable();

    /**
     * Returns the index in the parent array if an array cell value is represented.
     *
     * @return The index in the parent array or {@code null} if no array cell value is represented.
     */
    Term getArrayIndex();

    /**
     * Returns the human readable index in the parent array if an array cell value is represented.
     *
     * @return The human readable index in the parent array or {@code null} if no array cell value
     *         is represented.
     */
    String getArrayIndexString();

    /**
     * Checks if the current value is part of a parent array.
     *
     * @return {@code true} is array cell value, {@code false} is a "normal" value.
     */
    boolean isArrayIndex();

    /**
     * Returns the optional additional condition considered during value computation.
     *
     * @return The optional additional condition considered during value computation.
     */
    Term getAdditionalCondition();

    /**
     * Returns the parent {@link IExecutionValue} if available.
     *
     * @return The parent {@link IExecutionValue} if available and {@code null} otherwise.
     */
    IExecutionValue getParentValue();

    /**
     * Returns the possible values of this {@link IExecutionVariable}.
     *
     * @return The possible values of this {@link IExecutionVariable}.
     */
    IExecutionValue[] getValues() throws ProofInputException;

    /**
     * Creates recursive a term which can be used to determine the value of
     * {@link #getProgramVariable()}.
     *
     * @return The created term.
     */
    Term createSelectTerm();
}
