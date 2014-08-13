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

package de.hentschel.visualdbc.interactive.proving.ui.test.model;

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryMethod;

/**
 * Implementation of {@link IDSMethod} that allows interactive proofs
 * for test purpose.
 * @author Martin Hentschel
 */
public class LoggingMethod extends MemoryMethod {
   /**
    * Logs all executions of {@link #openInteractiveProof(String)}.
    */
   private List<String> openInteractiveProofLog = new LinkedList<String>();

   /**
    * An initial reference that is added to a new opened proof.
    */
   private IDSProvableReference initialReferenceToAdd;
   
   /**
    * Constructor.
    * @param signature The method signature.
    * @param returnType The return type.
    * @param visibility The visibility.
    */   
   public LoggingMethod(String signature, String returnType, DSVisibility visibility) {
      super(signature, returnType, visibility);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSProof removeProof(String obligation) {
      return super.removeProof(obligation);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSProof openInteractiveProof(String obligation) throws DSException, DSCanceledException {
      openInteractiveProofLog.add(obligation);
      IDSProof proof = getInteractiveProof(obligation);
      if (proof == null) {
         proof = new ExecutableProof();
         if (initialReferenceToAdd != null) {
            proof.getProofReferences().add(initialReferenceToAdd);
         }
         addProof(obligation, proof);
      }
      return proof;
   }

   /**
    * Returns the log of {@link #openInteractiveProof(String)}.
    * @return The log.
    */
   public List<String> getOpenInteractiveProofLog() {
      return openInteractiveProofLog;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasInteractiveProof(String obligation) throws DSException {
      return getInteractiveProof(obligation) != null;
   }

   /**
    * Returns the initial reference to add.
    * @return The initial reference to add.
    */
   public IDSProvableReference getInitialReferenceToAdd() {
      return initialReferenceToAdd;
   }

   /**
    * Sets the initial reference to add.
    * @param initialReferenceToAdd The initial reference to add.
    */
   public void setInitialReferenceToAdd(IDSProvableReference initialReferenceToAdd) {
      this.initialReferenceToAdd = initialReferenceToAdd;
   }
}