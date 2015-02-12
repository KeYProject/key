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
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.model.impl.AbstractSEDVariable;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;

/**
 * Implementation of {@link ISEDVariable} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYVariable extends AbstractSEDVariable {
   /**
    * The {@link IExecutionVariable} to represent in debug model.
    */
   private final IExecutionVariable executionVariable;
   
   /**
    * The contained {@link IValue}.
    */
   private IValue value;

   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this element is contained.
    * @param stackFrame The parent {@link IStackFrame} in which this {@link ISEDVariable} is shown.
    * @param executionVariable The {@link IExecutionVariable} to represent in debug model.
    */
   public KeYVariable(KeYDebugTarget target, IStackFrame stackFrame, IExecutionVariable executionVariable) {
      super(target, stackFrame);
      Assert.isNotNull(executionVariable);
      this.executionVariable = executionVariable;
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
   public String getName() throws DebugException {
      try {
         return executionVariable.getName();
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute name.", e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getReferenceTypeName() throws DebugException {
      if (getValue() != null) {
         String typeName = getValue().getReferenceTypeName();
         return typeName != null ? typeName : StringUtil.EMPTY_STRING;
      }
      else {
         return StringUtil.EMPTY_STRING;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasValueChanged() throws DebugException {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IValue getValue() throws DebugException {
      synchronized (this) {
         try {
            if (value == null && !executionVariable.isDisposed()) {
               IExecutionValue[] values = executionVariable.getValues();
               if (values.length == 0) {
                  throw new DebugException(LogUtil.getLogger().createErrorStatus("An IExecutionVariable must provide at least one IExecutionValue."));
               }
               else if (values.length == 1) {
                  value = new KeYValue(getDebugTarget(), this, values[0]);
               }
               else {
                  value = new KeYConditionalValues(getDebugTarget(), this, values);
               }
            }
            return value;
         }
         catch (ProofInputException e) {
            LogUtil.getLogger().logError(e);
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute value.", e));
         }
      }
   }

   /**
    * Returns the represented {@link IExecutionVariable}.
    * @return The represented {@link IExecutionVariable}.
    */
   public IExecutionVariable getExecutionVariable() {
      return executionVariable;
   }
}