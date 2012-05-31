package org.key_project.sed.core.model.memory;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.impl.AbstractSEDValue;

/**
 * Implementation of {@link ISEDValue} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryValue extends AbstractSEDValue {
   /**
    * The reference type name.
    */
   private String referenceTypeName;

   /**
    * The value string.
    */
   private String valueString;
   
   /**
    * The allocated flag.
    */
   private boolean allocated;
   
   /**
    * The contained variables.
    */
   private List<IVariable> variables = new LinkedList<IVariable>();
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this element is contained.
    */
   public SEDMemoryValue(ISEDDebugTarget target) {
      super(target);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getReferenceTypeName() throws DebugException {
      return referenceTypeName;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getValueString() throws DebugException {
      return valueString;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAllocated() throws DebugException {
      return allocated;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IVariable[] getVariables() throws DebugException {
      return variables.toArray(new IVariable[variables.size()]);
   }

   /**
    * Adds a new contained {@link IVariable}.
    * @param variable The {@link IVariable} to add.
    */
   public void addVariable(IVariable variable) {
      variables.add(variable);
   }

   /**
    * Sets the reference type name.
    * @param referenceTypeName The reference type name to set.
    */
   public void setReferenceTypeName(String referenceTypeName) {
      this.referenceTypeName = referenceTypeName;
   }

   /**
    * Sets the value string.
    * @param valueString The value string to set.
    */
   public void setValueString(String valueString) {
      this.valueString = valueString;
   }

   /**
    * Sets the allocated flag.
    * @param allocated The allocated flag to set.
    */
   public void setAllocated(boolean allocated) {
      this.allocated = allocated;
   }
}
