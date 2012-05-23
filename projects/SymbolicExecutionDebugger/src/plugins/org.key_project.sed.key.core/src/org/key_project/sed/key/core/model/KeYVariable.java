package org.key_project.sed.key.core.model;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IValue;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.model.impl.AbstractSEDVariable;

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
   private IExecutionVariable executionVariable;
   
   /**
    * The contained {@link IValue}.
    */
   private IValue value;

   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this element is contained.
    * @param executionVariable The {@link IExecutionVariable} to represent in debug model.
    */
   public KeYVariable(ISEDDebugTarget target, IExecutionVariable executionVariable) {
      super(target);
      Assert.isNotNull(executionVariable);
      this.executionVariable = executionVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      return executionVariable.getName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getReferenceTypeName() throws DebugException {
      return executionVariable.getTypeString();
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
      if (value == null) {
         value = new KeYValue(getDebugTarget(), executionVariable);
      }
      return value;
   }

   /**
    * Returns the represented {@link IExecutionVariable}.
    * @return The represented {@link IExecutionVariable}.
    */
   public IExecutionVariable getExecutionVariable() {
      return executionVariable;
   }
}
