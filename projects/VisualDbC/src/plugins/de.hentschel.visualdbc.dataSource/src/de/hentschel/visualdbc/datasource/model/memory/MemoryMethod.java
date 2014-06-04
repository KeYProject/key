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

package de.hentschel.visualdbc.datasource.model.memory;

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSMethod;

/**
 * Default implementation for an {@link IDSMethod} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryMethod extends MemoryOperation implements IDSMethod {
   /**
    * The return type.
    */
   private String returnType;
   
   /**
    * Is final?
    */
   private boolean isFinal;

   /**
    * Is abstract?
    */
   private boolean isAbstract;
   
   /**
    * Default constructor.
    */
   public MemoryMethod() {
   }

   /**
    * Constructor.
    * @param signature The method signature.
    * @param returnType The return type.
    * @param visibility The visibility.
    */
   public MemoryMethod(String signature, 
                       String returnType, 
                       DSVisibility visibility) {
      setSignature(signature);
      setReturnType(returnType);
      setVisibility(visibility);
   }

   /**
    * Constructor.
    * @param signature The method signature.
    * @param returnType The return type.
    * @param visibility The visibility.
    * @param isStatic Is static?
    */
   public MemoryMethod(String signature, 
                       String returnType, 
                       DSVisibility visibility, 
                       boolean isStatic) {
      setSignature(signature);
      setReturnType(returnType);
      setVisibility(visibility);
      setStatic(isStatic);
   }

   /**
    * Constructor.
    * @param signature The method signature.
    * @param returnType The return type.
    * @param visibility The visibility.
    * @param isStatic Is static?
    * @param isFinal Is final?
    */
   public MemoryMethod(String signature, 
                       String returnType, 
                       DSVisibility visibility, 
                       boolean isStatic, 
                       boolean isFinal) {
      setSignature(signature);
      setReturnType(returnType);
      setVisibility(visibility);
      setStatic(isStatic);
      setFinal(isFinal);
   }

   /**
    * Constructor.
    * @param signature The method signature.
    * @param returnType The return type.
    * @param visibility The visibility.
    * @param isStatic Is static?
    * @param isFinal Is final?
    * @param isAbstract Is abstract?
    */
   public MemoryMethod(String signature, 
                       String returnType, 
                       DSVisibility visibility, 
                       boolean isStatic, 
                       boolean isFinal, 
                       boolean isAbstract) {
      setSignature(signature);
      setReturnType(returnType);
      setVisibility(visibility);
      setStatic(isStatic);
      setFinal(isFinal);
      setAbstract(isAbstract);
   }

   /**
    * Sets the return type.
    * @param returnType The return type to set.
    */
   public void setReturnType(String returnType) {
      this.returnType = returnType;
   }

   /**
    * Sets the abstract flag.
    * @param isAbstract The abstract flag to set.
    */
   public void setAbstract(boolean isAbstract) {
      this.isAbstract = isAbstract;
   }

   /**
    * Sets the final flag.
    * @param isFinal The final flag to set.
    */
   public void setFinal(boolean isFinal) {
      this.isFinal = isFinal;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getReturnType() {
      return returnType;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isFinal() {
      return isFinal;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAbstract() {
      return isAbstract;
   }
}