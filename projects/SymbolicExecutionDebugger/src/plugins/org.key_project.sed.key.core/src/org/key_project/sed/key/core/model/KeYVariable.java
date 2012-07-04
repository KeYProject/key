package org.key_project.sed.key.core.model;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.model.impl.AbstractSEDVariable;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.init.ProofInputException;
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
    * @param target The {@link KeYDebugTarget} in that this element is contained.
    * @param executionVariable The {@link IExecutionVariable} to represent in debug model.
    */
   public KeYVariable(KeYDebugTarget target, IExecutionVariable executionVariable) {
      super(target);
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
      try {
         String typeName = executionVariable.getTypeString();
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
