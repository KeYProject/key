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

package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Default implementation of {@link ISymbolicAssociation}.
 * @author Martin Hentschel
 */
public class SymbolicAssociation implements ISymbolicAssociation {
   /**
    * The array index.
    */
   private int arrayIndex;
   
   /**
    * The {@link IProgramVariable}.
    */
   private IProgramVariable programVariable;
   
   /**
    * The target {@link ISymbolicObject}.
    */
   private ISymbolicObject target;
   /**
    * Constructor.
    * @param arrayIndex The array index.
    * @param target The target {@link ISymbolicObject}.
    */
   public SymbolicAssociation(int arrayIndex, ISymbolicObject target) {
      assert target != null;
      this.arrayIndex = arrayIndex;
      this.target = target;
   }
   
   /**
    * Constructor.
    * @param programVariable The {@link IProgramVariable}.
    * @param target The target {@link ISymbolicObject}.
    */
   public SymbolicAssociation(IProgramVariable programVariable, ISymbolicObject target) {
      assert programVariable != null;
      assert target != null;
      this.programVariable = programVariable;
      this.target = target;
      this.arrayIndex = -1;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      if (isArrayIndex()) {
         return "[" + getArrayIndex() + "]";
      }
      else {
         return getProgramVariableString();
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isArrayIndex() {
      return arrayIndex >= 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getArrayIndex() {
      return arrayIndex;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramVariable getProgramVariable() {
      return programVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getProgramVariableString() {
      return SymbolicExecutionUtil.getDisplayString(programVariable);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISymbolicObject getTarget() {
      return target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Association " + getName() + " to " + getTarget();
   }
}