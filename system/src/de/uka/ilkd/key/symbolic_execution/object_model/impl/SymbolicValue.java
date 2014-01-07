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
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Default implementation of {@link ISymbolicValue}.
 * @author Martin Hentschel
 */
public class SymbolicValue extends AbstractElement implements ISymbolicValue {
   /**
    * The {@link Services} to use.
    */
   private final Services services;

   /**
    * The array index.
    */
   private final int arrayIndex;
   
   /**
    * The {@link IProgramVariable}.
    */
   private final IProgramVariable programVariable;
   
   /**
    * The value {@link Term}.
    */
   private final Term value;
   
   /**
    * The optional condition under which this value is valid.
    */
   private final Term condition;

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param arrayIndex The array index.
    * @param value The value {@link Term}.
    * @param condition The optional condition under which this value is valid.
    * @param settings The {@link IModelSettings} to use.
    */
   public SymbolicValue(Services services, 
                        int arrayIndex, 
                        Term value, 
                        Term condition, 
                        IModelSettings settings) {
      super(settings);
      assert services != null;
      assert arrayIndex >= 0;
      this.services = services;
      this.programVariable = null;
      this.arrayIndex = arrayIndex;
      this.value = value;
      this.condition = condition;
   }

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param programVariable The {@link IProgramVariable}.
    * @param value The value {@link Term}.
    * @param condition The optional condition under which this value is valid.
    * @param settings The {@link IModelSettings} to use.
    */
   public SymbolicValue(Services services, 
                        IProgramVariable programVariable, 
                        Term value, 
                        Term condition, 
                        IModelSettings settings) {
      super(settings);
      assert services != null;
      assert programVariable != null;
      this.services = services;
      this.programVariable = programVariable;
      this.value = value;
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
   public Term getValue() {
      return value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getValueString() {
      return formatTerm(value, services);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Sort getType() {
      return value != null ? value.sort() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getTypeString() {
      Sort sort = getType();
      return sort != null ? sort.toString() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Value of " + getName() + " is " + getValueString();
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
}