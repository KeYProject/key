/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package de.hentschel.visualdbc.datasource.model.implementation;

import java.util.HashMap;
import java.util.Map;

import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Provides a basic implementation of an {@link IDSProvable}.
 * @author Martin Hentschel
 */
public abstract class AbstractDSProvable implements IDSProvable {
   /**
    * Contains the opened {@link IDSProof}s registered by their obligation.
    */
   private Map<String, IDSProof> proofs = new HashMap<String, IDSProof>();
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isValidObligation(String obligation) throws DSException {
      return getObligations().contains(obligation);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSProof openInteractiveProof(String obligation) throws DSException, DSCanceledException {
      throw new DSException("Interactive proof solving is not supported.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSProof getInteractiveProof(String obligation) throws DSException {
      return proofs.get(obligation);
   }
   
   /**
    * Registers the new opened {@link IDSProof}.
    * @param obligation The used obligation.
    * @param proof The opened proof.
    */
   protected void addProof(String obligation, IDSProof proof) {
      proofs.put(obligation, proof);
   }
   
   /**
    * Removes a opened {@link IDSProof}.
    * @param obligation The obligation of the proof to remove.
    * @return The removed {@link IDSProof} or {@code null} if no one was removed.
    */
   protected IDSProof removeProof(String obligation) {
      return proofs.remove(obligation);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasInteractiveProof(String obligation) throws DSException {
      return false;
   }
}