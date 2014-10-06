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

package org.key_project.sed.core.model.memory;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.ISEDConstraint;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;
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
    * Is object or only an object attribute?
    */
   private boolean object;
   
   /**
    * Is multi valued?
    */
   private boolean multiValued;

   /**
    * The contained variables.
    */
   private final List<IVariable> variables = new LinkedList<IVariable>();
   
   /**
    * All the relevant constraints.
    */
   private final List<ISEDConstraint> relevantConstaints = new LinkedList<ISEDConstraint>();
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this element is contained.
    * @param parent The parent {@link ISEDVariable}.
    */
   public SEDMemoryValue(ISEDDebugTarget target, ISEDVariable parent) {
      super(target, parent);
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
    * {@inheritDoc}
    */
   @Override
   public boolean isMultiValued() throws DebugException {
      return multiValued;
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

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isObject() {
      return object;
   }

   /**
    * Defines if this value is an object or just an object attribute.
    * @param object {@code true} is ojbect, {@code false} is object attribute.
    */
   public void setObject(boolean object) {
      this.object = object;
   }
   
   /**
    * Defines if this value is multi valued.
    * @param multiValued Multi valued?
    */
   public void setMultiValued(boolean multiValued) {
      this.multiValued = multiValued;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setId(String id) {
      super.setId(id);
   }

   /**
    * Adds the given relevant {@link ISEDConstraint}.
    * @param constraint The relevant {@link ISEDConstraint} to add.
    */
   public void addRelevantConstraint(ISEDConstraint constraint) {
      if (constraint != null) {
         relevantConstaints.add(constraint);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDConstraint[] getRelevantConstraints() throws DebugException {
      return relevantConstaints.toArray(new ISEDConstraint[relevantConstaints.size()]);
   }
}