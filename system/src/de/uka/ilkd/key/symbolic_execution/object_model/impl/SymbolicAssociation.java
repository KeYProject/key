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

package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Default implementation of {@link ISymbolicAssociation}.
 * @author Martin Hentschel
 */
public class SymbolicAssociation extends AbstractElement implements ISymbolicAssociation {
   /**
    * The {@link Services} to use.
    */
   private final Services services;

   /**
    * The array index.
    */
   private final Term arrayIndex;
   
   /**
    * The {@link IProgramVariable}.
    */
   private final IProgramVariable programVariable;
   
   /**
    * The target {@link ISymbolicObject}.
    */
   private final ISymbolicObject target;
   
   /**
    * The optional condition under which this association is valid.
    */
   private final Term condition;
   
   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param arrayIndex The array index.
    * @param target The target {@link ISymbolicObject}.
    * @param condition The optional condition under which this association is valid.
    * @param settings The {@link IModelSettings} to use.
    */
   public SymbolicAssociation(Services services, 
                              Term arrayIndex, 
                              ISymbolicObject target, 
                              Term condition,
                              IModelSettings settings) {
      super(settings);
      assert services != null;
      assert target != null;
      this.services = services;
      this.programVariable = null;
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
    * @param settings The {@link IModelSettings} to use.
    */
   public SymbolicAssociation(Services services, 
                              IProgramVariable programVariable, 
                              ISymbolicObject target, 
                              Term condition,
                              IModelSettings settings) {
      super(settings);
      assert services != null;
      assert programVariable != null;
      assert target != null;
      this.services = services;
      this.programVariable = programVariable;
      this.target = target;
      this.arrayIndex = null;
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
         sb.append(getArrayIndexString());
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
      return arrayIndex != null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getArrayIndex() {
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
      return condition != null ? formatTerm(condition, services) : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getArrayIndexString() {
      return arrayIndex != null ? formatTerm(arrayIndex, services) : null;
   }
}