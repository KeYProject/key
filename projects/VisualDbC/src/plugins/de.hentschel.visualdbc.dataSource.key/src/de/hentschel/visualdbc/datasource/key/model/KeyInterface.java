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

package de.hentschel.visualdbc.datasource.key.model;

import org.eclipse.core.runtime.Assert;

import de.hentschel.visualdbc.datasource.key.intern.helper.OpenedProof;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInterface;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

/**
 * Special KeY implementation of {@link IDSInterface}.
 * @author Martin Hentschel
 */
public class KeyInterface extends MemoryInterface {
   /**
    * The {@link KeYJavaType}.
    */
   private KeYJavaType type;
   
   /**
    * The {@link KeyConnection} that has created this instance.
    */
   private KeyConnection connection;

   /**
    * Constructor.
    * @param connection The {@link KeyConnection} that has created this instance.
    * @param type The {@link KeYJavaType}.
    */
   public KeyInterface(KeyConnection connection,
                       KeYJavaType type) {
      super();
      Assert.isNotNull(connection);
      Assert.isNotNull(type);
      this.connection = connection;
      this.type = type;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IDSProof openInteractiveProof(String obligation) throws DSException, DSCanceledException {
      if (connection.isInteractive()) {
         // Make sure that a proof is not already opened.
         KeyProof oldDsProof = getInteractiveProof(obligation);
         if (!isProofValid(oldDsProof)) {
            // Open new proof.
            OpenedProof proofResult = connection.openProof(type, null, null, obligation);
            if (proofResult != null) {
               KeyProof dsProof = new KeyProof(proofResult, connection);
               addProof(obligation, dsProof);
               connection.fireInteractiveProofStarted(dsProof);
               return dsProof;
            }
            else {
               throw new DSException("No proof opened. Reason is unknown.");
            }
         }
         else {
            // Select proof in tree
            connection.selectProof(oldDsProof.getProof());
            return oldDsProof;
         }
      }
      else {
         throw new DSException("Interactive proof solving is only supported in interactive mode.");
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeyProof getInteractiveProof(String obligation) throws DSException {
      return (KeyProof)super.getInteractiveProof(obligation);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasInteractiveProof(String obligation) throws DSException {
      KeyProof oldDsProof = getInteractiveProof(obligation);
      return isProofValid(oldDsProof);
   }
   
   /**
    * Checks if the KeY proof instance is still valid.
    * Valid means the proof is available in the user interface for the user.
    * @param proof The {@link KeyProof} to check.
    * @return {@code true} = is valid, {@code false} = is not valid
    */
   protected boolean isProofValid(KeyProof proof) {
      return proof != null && !proof.getProof().isDisposed();
   }
}