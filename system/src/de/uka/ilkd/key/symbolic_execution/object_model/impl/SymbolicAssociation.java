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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Default implementation of {@link ISymbolicAssociation}.
 * @author Martin Hentschel
 */
public class SymbolicAssociation implements ISymbolicAssociation {
   /**
    * The {@link Services} to use.
    */
   private Services services;

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
    * The optional condition under which this association is valid.
    */
   private Term condition;
   
   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param arrayIndex The array index.
    * @param target The target {@link ISymbolicObject}.
    * @param condition The optional condition under which this association is valid.
    */
   public SymbolicAssociation(Services services, int arrayIndex, ISymbolicObject target, Term condition) {
      assert services != null;
      assert target != null;
      this.services = services;
      this.arrayIndex = arrayIndex;
      this.target = target;
      this.condition = condition;
   }
   
   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param programVariable The {@link IProgramVariable}.
    * @param target The target {@link ISymbolicObject}.
    * @param condition The optional condition under which this association is valid.
    */
   public SymbolicAssociation(Services services, IProgramVariable programVariable, ISymbolicObject target, Term condition) {
      assert services != null;
      assert programVariable != null;
      assert target != null;
      this.services = services;
      this.programVariable = programVariable;
      this.target = target;
      this.arrayIndex = -1;
      this.condition = condition;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      StringBuffer sb = new StringBuffer();
      if (isArrayIndex()) {
         sb.append("[");
         sb.append(getArrayIndex());
         sb.append("]");
      }
      else {
         sb.append(getProgramVariableString());
      }
      if (condition != null) {
         sb.append(" {");
         sb.append(getConditionString());
         sb.append("}");
      }
      return sb.toString();
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

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getCondition() {
      return condition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getConditionString() {
      if (condition != null) {
         StringBuffer sb = ProofSaver.printTerm(condition, services, true);
         return sb.toString();
      }
      else {
         return null;
      }
   }
}