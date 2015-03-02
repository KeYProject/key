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
 * based on KeY which represents an conditional {@link IExecutionValue} instead
 * of a real variable ({@link IExecutionVariable}).
 * @author Martin Hentschel
 */
public class KeYConditionalValueVariable extends AbstractSEDVariable {
   /**
    * The conditional {@link IExecutionValue} to represent in debug model.
    */
   private final IExecutionValue executionValue;
   
   /**
    * The contained {@link IValue}.
    */
   private IValue value;

   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this element is contained.
    * @param stackFrame The parent {@link IStackFrame} in which this {@link ISEDVariable} is shown.
    * @param executionValue The conditional {@link IExecutionValue} to represent in debug model.
    */
   public KeYConditionalValueVariable(KeYDebugTarget target, IStackFrame stackFrame, IExecutionValue executionValue) {
      super(target, stackFrame);
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
   public String getName() throws DebugException {
      try {
         return executionValue.getName();
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
         if (value == null) {
            value = new KeYValue(getDebugTarget(), this, executionValue);
         }
         return value;
      }
   }

   /**
    * Returns the represented {@link IExecutionValue}.
    * @return The represented {@link IExecutionValue}.
    */
   public IExecutionValue getExecutionValue() {
      return executionValue;
   }
}