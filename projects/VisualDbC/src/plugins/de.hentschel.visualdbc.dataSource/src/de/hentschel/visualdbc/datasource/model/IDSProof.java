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

package de.hentschel.visualdbc.datasource.model;

import java.util.List;

import de.hentschel.visualdbc.datasource.model.event.IDSProofListener;

/**
 * Represents a proof on the data source.
 * @author Martin Hentschel
 */
public interface IDSProof {
   /**
    * Checks if the proof is closed.
    * @return {@code true} = is closed, {@code false} = is open.
    */
   public boolean isClosed();
   
   /**
    * Adds the listener.
    * @param l The listener to add.
    */
   public void addProofListener(IDSProofListener l);

   /**
    * Removes the listener.
    * @param l The listener to remove.
    */
   public void removeProofListener(IDSProofListener l);
   
   /**
    * Returns all registered listeners.
    * @return The registered listeners.
    */
   public IDSProofListener[] getProofListeners();
   
   /**
    * Returns all available proof references.
    * @return The available proof references.
    */
   public List<IDSProvableReference> getProofReferences();
}
