// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionVariable;

/**
 * <p>
 * A variable value pair contained in an {@link IExecutionStateNode}, e.g.
 * the method parameter {@code int x = 42;} will have the variable value pair
 * {@code x = 42}. This class represents the variable ({@code x}) which is represented
 * while its values are reprented as child {@link IExecutionValue} instances.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionVariable} which
 * is instantiated lazily by the {@link IExecutionStateNode} implementations.
 * </p>
 * @author Martin Hentschel
 * @see IExecutionStateNode
 * @see IExecutionValue
 * @see ExecutionVariable
 */
public interface IExecutionVariable extends IExecutionElement {
   /**
    * Returns the {@link IProgramVariable} which contains the represented value.
    * @return The {@link IProgramVariable} which contains the represented value.
    */
   public IProgramVariable getProgramVariable();
   
   /**
    * Returns the index in the parent array if an array cell value is represented.
    * @return The index in the parent array or {@code -1} if no array cell value is represented.
    */
   public int getArrayIndex();
   
   /**
    * Checks if the current value is part of a parent array.
    * @return {@code true} is array cell value, {@code false} is a "normal" value.
    */
   public boolean isArrayIndex();
   
   /**
    * Returns the parent {@link IExecutionValue} if available.
    * @return The parent {@link IExecutionValue} if available and {@code null} otherwise.
    */
   public IExecutionValue getParentValue();
   
   /**
    * Returns the possible values of this {@link IExecutionVariable}.
    * @return The possible values of this {@link IExecutionVariable}.
    */
   public IExecutionValue[] getValues() throws ProofInputException;
}