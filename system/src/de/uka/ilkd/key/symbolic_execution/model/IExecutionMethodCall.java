// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodCall;

/**
 * <p>
 * A node in the symbolic execution tree which represents a method call,
 * e.g. {@code foo()}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionMethodCall} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionMethodCall
 */
public interface IExecutionMethodCall extends IExecutionStateNode<MethodBodyStatement> {
   /**
    * Returns the {@link MethodReference} instance of the called method.
    * @return The {@link MethodReference} of the called method.
    */
   public MethodReference getMethodReference();
   
   /**
    * Returns the called {@link IProgramMethod}.
    * @return The called {@link IProgramMethod}.
    */
   public IProgramMethod getProgramMethod();
   
   /**
    * Checks if an implicit constructor is called.
    * @return {@code true} implicit constructor is called, {@code false} method or explicit constructor is called.
    */
   public boolean isImplicitConstructor();
   
   /**
    * Returns a copy of the {@link MethodReference} which calls the
    * explicit constructor instead of the implicit constructor.
    * @return The {@link MethodReference} to the explicit constructor or {@code null} if no constructor is called.
    */
   public MethodReference getExplicitConstructorMethodReference();

   /**
    * Returns the explicit constructor.
    * @return The explicit constructor or {@code null} if no constructor is called.
    */
   public IProgramMethod getExplicitConstructorProgramMethod();
   
   /**
    * Returns the up to now discovered {@link IExecutionBaseMethodReturn}s.
    * @return The up to now discovered {@link IExecutionBaseMethodReturn}s.
    */
   public ImmutableList<IExecutionBaseMethodReturn<?>> getMethodReturns();
}