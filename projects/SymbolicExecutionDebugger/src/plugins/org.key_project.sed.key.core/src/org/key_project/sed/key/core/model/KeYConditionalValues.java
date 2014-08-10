/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.model;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.impl.AbstractSEDValue;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;

/**
 * Implementation of {@link ISEDValue} for the symbolic execution debugger (SED)
 * based on KeY which represents multiple conditional {@link IExecutionValue}s.
 * @author Martin Hentschel
 */
public class KeYConditionalValues extends AbstractSEDValue {
   /**
    * The constant name which is shown to a user to represent conditional values.
    */
   public static final String CONDITIONAL_VALUES = "<conditional values>";
   
   /**
    * The {@link IExecutionValue}s to represent.
    */
   private IExecutionValue[] values;
   
   /**
    * The contained child {@link KeYConditionalValueVariable}s.
    */
   private KeYConditionalValueVariable[] variables;

   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this element is contained.
    * @param values The {@link IExecutionValue}s to represent.
    */
   public KeYConditionalValues(KeYDebugTarget target, IExecutionValue[] values) {
      super(target);
      Assert.isNotNull(values);
      Assert.isTrue(values.length >= 2);
      this.values = values;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public KeYDebugTarget getDebugTarget() {
      return (KeYDebugTarget)super.getDebugTarget();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYConditionalValueVariable[] getVariables() throws DebugException {
      synchronized (this) {
         if (variables == null) {
            List<KeYConditionalValueVariable> result = new ArrayList<KeYConditionalValueVariable>(values.length);
            for (IExecutionValue value : values){
               result.add(new KeYConditionalValueVariable(getDebugTarget(), value));
            }
            variables = result.toArray(new KeYConditionalValueVariable[result.size()]);
         }
         return variables;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getReferenceTypeName() throws DebugException {
      return StringUtil.EMPTY_STRING;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getValueString() throws DebugException {
      return CONDITIONAL_VALUES;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isObject() throws DebugException {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAllocated() throws DebugException {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isMultiValued() throws DebugException {
      return true;
   }
}