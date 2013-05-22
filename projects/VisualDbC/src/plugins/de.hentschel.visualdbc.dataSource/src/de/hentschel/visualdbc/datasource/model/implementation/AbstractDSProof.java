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

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.event.DSProofEvent;
import de.hentschel.visualdbc.datasource.model.event.IDSProofListener;

/**
 * Provides a basic implementation of an {@link IDSProof}.
 * @author Martin Hentschel
 */
public abstract class AbstractDSProof implements IDSProof {
   /**
    * Contains all registered listeners.
    */
   private List<IDSProofListener> listeners = new LinkedList<IDSProofListener>(); 

   /**
    * {@inheritDoc}
    */
   @Override
   public void addProofListener(IDSProofListener l) {
      if (l != null) {
         listeners.add(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeProofListener(IDSProofListener l) {
      if (l != null) {
         listeners.remove(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSProofListener[] getProofListeners() {
      return listeners.toArray(new IDSProofListener[listeners.size()]);
   }
   
   /**
    * Fires the event {@link IDSProofListener#proofClosed(DSProofEvent)}
    * to all registered listeners.
    * @param e The event to fire.
    */
   protected void fireProofClosed(DSProofEvent e) {
      IDSProofListener[] allListeners = getProofListeners();
      for (IDSProofListener l : allListeners) {
         l.proofClosed(e);
      }
   }
   
   /**
    * Fires the event {@link IDSProofListener#referencesChanged(DSProofEvent)}
    * to all registered listeners.
    * @param e The event to fire.
    */
   protected void fireReferencesChanged(DSProofEvent e) {
      IDSProofListener[] allListeners = getProofListeners();
      for (IDSProofListener l : allListeners) {
         l.referencesChanged(e);
      }
   }
}