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

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSOperation;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSOperation;

/**
 * Default implementation for an {@link IDSOperation} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryOperation extends AbstractDSOperation {
   /**
    * The constructor signature.
    */
   private String signature;
   
   /**
    * The visibility.
    */
   private DSVisibility visibility;

   /**
    * Is static?
    */
   private boolean isStatic;

   /**
    * Contains all operation contracts.
    */
   private List<IDSOperationContract> operationContracts = new LinkedList<IDSOperationContract>();
   
   /**
    * All available obligations.
    */
   private List<String> obligations = new LinkedList<String>();
   
   /**
    * The parent.
    */
   private IDSType parent;
   
   /**
    * Default constructor.
    */
   public MemoryOperation() {
   }
   
   /**
    * Constructor.
    * @param signature The constructor signature.
    * @param visibility The visibility.
    */
   public MemoryOperation(String signature, DSVisibility visibility) {
      setSignature(signature);
      setVisibility(visibility);
   }

   /**
    * Sets the signature.
    * @param signature The signature to set.
    */
   public void setSignature(String signature) {
      this.signature = signature;
   }

   /**
    * Sets the visibility.
    * @param visibility The visibility to set.
    */
   public void setVisibility(DSVisibility visibility) {
      this.visibility = visibility;
   }

   /**
    * Sets the static flag.
    * @param isStatic The flag to set.
    */
   public void setStatic(boolean isStatic) {
      this.isStatic = isStatic;
   }

   /**
    * Sets the parent.
    * @param parent The parent to set.
    */
   public void setParent(IDSType parent) {
      this.parent = parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getSignature() {
      return signature;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public DSVisibility getVisibility() {
      return visibility;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isStatic() {
      return isStatic;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSOperationContract> getOperationContracts() {
      return operationContracts;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<String> getObligations() {
      return obligations;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSType getParent() {
      return parent;
   }
   
   /**
    * Adds the operation contract and updates his parent reference.
    * @param oc The operation contract to add.
    */
   public void addOperationContract(MemoryOperationContract oc) {
      operationContracts.add(oc);
      oc.setParent(this);
   }
}