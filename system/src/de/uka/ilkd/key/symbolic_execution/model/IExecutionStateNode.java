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
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;

/**
 * A special {@link IExecutionNode} for nodes in the symbolic execution tree
 * which represents a statement in the code. Such nodes also have a state
 * (e.g. heap values).
 * @author Martin Hentschel
 */
public interface IExecutionStateNode<S extends SourceElement> extends IExecutionNode {
   /**
    * Returns the active statement which is executed in the code.
    * @return The active statement which is executed in the code.
    */
   public S getActiveStatement();
   
   /**
    * Returns the {@link PositionInfo} of {@link #getActiveStatement()}.
    * @return The {@link PositionInfo} of {@link #getActiveStatement()}.
    */
   public PositionInfo getActivePositionInfo();
   
   /**
    * Returns the variable value pairs of the current state.
    * @return The variable value pairs.
    */
   public IExecutionVariable[] getVariables();
   
   /**
    * Returns the number of memory layouts.
    * @return The number of memory layouts.
    * @throws ProofInputException Occurred Exception.
    */
   public int getLayoutsCount() throws ProofInputException;
   
   /**
    * Returns the equivalence classes of the memory layout with the given index.
    * @param layoutIndex The index of the memory layout.
    * @return The equivalence classes of the memory layout at the given index.
    * @throws ProofInputException Occurred Exception.
    */
   public ImmutableList<ISymbolicEquivalenceClass> getLayoutsEquivalenceClasses(int layoutIndex) throws ProofInputException;
   
   /**
    * Returns the initial memory layout before the method was executed.
    * @param layoutIndex The index of the memory layout.
    * @return The initial memory layout at the given index.
    * @throws ProofInputException Occurred Exception.
    */
   public ISymbolicLayout getInitialLayout(int layoutIndex) throws ProofInputException;
   
   /**
    * Returns the current memory layout which shows the memory
    * structure before the current node in the symbolic execution tree is executed.
    * @param layoutIndex The index of the memory layout.
    * @return The current memory layout at the given index.
    * @throws ProofInputException Occurred Exception.
    */
   public ISymbolicLayout getCurrentLayout(int layoutIndex) throws ProofInputException;
}