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

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.impl.AbstractSEDValue;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;

/**
 * Implementation of {@link ISEDValue} for the symbolic execution debugger (SED)
 * based on KeY which represents one {@link IExecutionValue}.
 * @author Martin Hentschel
 */
public class KeYValue extends AbstractSEDValue {
   /**
    * The constant name which is shown to a user if the value is unknown.
    */
   public static final String UNKNOWN_VALUE = "<unknown value>";

   /**
    * The {@link IExecutionValue} to represent in debug model.
    */
   private final IExecutionValue executionValue;
   
   /**
    * The contained child {@link KeYVariable}s.
    */
   private KeYVariable[] variables;
   
   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this element is contained.
    * @param executionValue The {@link IExecutionValue} to represent in debug model.
    */
   public KeYValue(KeYDebugTarget target, IExecutionValue executionValue) {
      super(target);
      Assert.isNotNull(executionValue);
      this.executionValue = executionValue;
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
   public String getReferenceTypeName() throws DebugException {
      try {
         String typeName = executionValue.getTypeString();
         return typeName != null ? typeName : StringUtil.EMPTY_STRING;
      }
      catch (ProofInputException e) {
         LogUtil.getLogger().logError(e);
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute reference type name.", e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getValueString() throws DebugException {
      try {
         return !executionValue.isValueUnknown() ? 
                executionValue.getValueString() : 
                UNKNOWN_VALUE;
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute variable value.", e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYVariable[] getVariables() throws DebugException {
      synchronized (this) {
         try {
            if (variables == null) {
               IExecutionVariable[] executionVariables = executionValue.getChildVariables();
               if (executionVariables != null) {
                  variables = new KeYVariable[executionVariables.length];
                  for (int i = 0; i < executionVariables.length; i++) {
                     variables[i] = new KeYVariable(getDebugTarget(), executionVariables[i]);
                  }
               }
               else {
                  variables = new KeYVariable[0];
               }
            }
            return variables;
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute child variables.", e));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasVariables() throws DebugException {
      return !executionValue.isDisposed() && 
             super.hasVariables(); 
             
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAllocated() throws DebugException {
      return true;
   }

   /**
    * Returns the represented {@link IExecutionValue}.
    * @return The represented {@link IExecutionValue}.
    */
   public IExecutionValue getExecutionValue() {
      return executionValue;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isObject() throws DebugException {
      try {
         return getExecutionValue().isValueAnObject();
      }
      catch (ProofInputException e) {
         LogUtil.getLogger().logError(e);
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't check is object.", e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isMultiValued() throws DebugException {
      return false;
   }
}