/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodCall;

import org.key_project.util.collection.ImmutableList;

/**
 * <p>
 * A node in the symbolic execution tree which represents a method call, e.g. {@code foo()}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionMethodCall} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionMethodCall
 */
public interface IExecutionMethodCall extends IExecutionNode<MethodBodyStatement> {
    /**
     * Returns the {@link MethodReference} instance of the called method.
     *
     * @return The {@link MethodReference} of the called method.
     */
    MethodReference getMethodReference();

    /**
     * Returns the called {@link IProgramMethod}.
     *
     * @return The called {@link IProgramMethod}.
     */
    IProgramMethod getProgramMethod();

    /**
     * Checks if an implicit constructor is called.
     *
     * @return {@code true} implicit constructor is called, {@code false} method or explicit
     *         constructor is called.
     */
    boolean isImplicitConstructor();

    /**
     * Returns a copy of the {@link MethodReference} which calls the explicit constructor instead of
     * the implicit constructor.
     *
     * @return The {@link MethodReference} to the explicit constructor or {@code null} if no
     *         constructor is called.
     */
    MethodReference getExplicitConstructorMethodReference();

    /**
     * Returns the explicit constructor.
     *
     * @return The explicit constructor or {@code null} if no constructor is called.
     */
    IProgramMethod getExplicitConstructorProgramMethod();

    /**
     * Returns the up to now discovered {@link IExecutionBaseMethodReturn}s.
     *
     * @return The up to now discovered {@link IExecutionBaseMethodReturn}s.
     */
    ImmutableList<IExecutionBaseMethodReturn<?>> getMethodReturns();
}
