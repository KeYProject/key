package org.key_project.sed.key.core.model;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.impl.AbstractSEDValue;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;

/**
 * Implementation of {@link ISEDValue} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYValue extends AbstractSEDValue {
   /**
    * The {@link IExecutionVariable} to represent in debug model.
    */
   private IExecutionVariable executionVariable;
   
   /**
    * The contained child {@link KeYVariable}s.
    */
   private KeYVariable[] variables;
   
   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this element is contained.
    * @param executionVariable The {@link IExecutionVariable} to represent in debug model.
    */
   public KeYValue(KeYDebugTarget target, IExecutionVariable executionVariable) {
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
   public String getValueString() throws DebugException {
      try {
         return executionVariable.getValueString();
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
               IExecutionVariable[] executionVariables = executionVariable.getChildVariables();
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
      return super.hasVariables() && getDebugTarget().getLaunchSettings().isShowVariablesOfSelectedDebugNode();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAllocated() throws DebugException {
      return true;
   }

   /**
    * Returns the represented {@link IExecutionVariable}.
    * @return The represented {@link IExecutionVariable}.
    */
   public IExecutionVariable getExecutionVariable() {
      return executionVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isObject() throws DebugException {
      try {
         Term value = getExecutionVariable().getValue();
         Sort sort = value.sort();
         KeYJavaType kjt = getExecutionVariable().getServices().getJavaInfo().getKeYJavaType(sort);
         TypeConverter typeConverter = getExecutionVariable().getServices().getTypeConverter();
         return typeConverter.isReferenceType(kjt) && // Check if the value is a reference type
                (!(kjt.getJavaType() instanceof TypeDeclaration) || // check if the value is a library class which should be ignored
                !((TypeDeclaration)kjt.getJavaType()).isLibraryClass());
      }
      catch (ProofInputException e) {
         LogUtil.getLogger().logError(e);
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't check is object.", e));
      }
   }
}
