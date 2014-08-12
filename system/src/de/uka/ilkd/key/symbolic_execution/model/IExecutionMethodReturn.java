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

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;

/**
 * <p>
 * A node in the symbolic execution tree which represents a method return,
 * e.g. {@code return 42}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionMethodReturn} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionMethodReturn
 */
public interface IExecutionMethodReturn extends IExecutionStateNode<SourceElement> {
   /**
    * A reference to the {@link IExecutionMethodCall} which is now returned.
    * @return The call of the now returned method.
    */
   public IExecutionMethodCall getMethodCall();
   
   /**
    * Returns a human readable signature which describes this element.
    * @return The human readable signature which describes this element.
    * @throws ProofInputException Occurred Exception.
    */
   public String getSignature() throws ProofInputException;
   
   /**
    * Returns the human readable node name including the return value ({@link #getReturnValues()}).
    * @return The human readable node name including the return value.
    * @throws ProofInputException Occurred Exception.
    */
   public String getNameIncludingReturnValue() throws ProofInputException;
   
   /**
    * Returns the human readable signature including the return value ({@link #getReturnValues()}).
    * @return The human readable signature including the return value.
    * @throws ProofInputException Occurred Exception.
    */
   public String getSignatureIncludingReturnValue() throws ProofInputException;

   /**
    * Checks if the values of {@link #getReturnValues()} are already computed.
    * @return {@code true} value of {@link #getReturnValues()} are already computed, {@code false} values of {@link #getReturnValues()} needs to be computed.
    */
   public boolean isReturnValuesComputed();
   
   /**
    * Returns the possible return values.
    * @return The possible return values.
    * @throws ProofInputException Occurred Exception.
    */
   public IExecutionMethodReturnValue[] getReturnValues() throws ProofInputException;
   
   /**
    * Returns the condition under which this method return is reached from
    * the calling {@link IExecutionMethodCall}.
    * @return The method return condition to reach this node from its {@link IExecutionMethodCall} as {@link Term}.
    */
   public Term getMethodReturnCondition() throws ProofInputException;
   
   /**
    * Returns the human readable condition under which this method return is reached from
    * the calling {@link IExecutionMethodCall}.
    * @return The human readable method return condition to reach this node from its {@link IExecutionMethodCall}.
    */
   public String getFormatedMethodReturnCondition() throws ProofInputException;
}