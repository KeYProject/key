/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.model.memory;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSProof;

/**
 * Default implementation for an {@link IDSProof} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryProof extends AbstractDSProof {
   /**
    * Contains the available proof references.
    */
   private List<IDSProvableReference> proofReferences = Collections.synchronizedList(new LinkedList<IDSProvableReference>());

   /**
    * Indicates that the proof is closed.
    */
   private boolean closed;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSProvableReference> getProofReferences() {
      return proofReferences;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isClosed() {
      return closed;
   }

   /**
    * Sets the proof closed status.
    * @param closed The closed status to set.
    */
   public void setClosed(boolean closed) {
      this.closed = closed;
   }
}
