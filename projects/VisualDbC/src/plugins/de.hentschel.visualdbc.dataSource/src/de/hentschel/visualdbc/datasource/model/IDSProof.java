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