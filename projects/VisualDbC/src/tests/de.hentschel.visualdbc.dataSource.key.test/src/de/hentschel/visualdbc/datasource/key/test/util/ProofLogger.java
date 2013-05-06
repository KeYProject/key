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

package de.hentschel.visualdbc.datasource.key.test.util;

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.event.DSProofEvent;
import de.hentschel.visualdbc.datasource.model.event.IDSProofListener;

/**
 * Implementation of {@link IDSProofListener} that logs all occurred events
 * in the main memory.
 * @author Martin Hentschel
 */
public class ProofLogger implements IDSProofListener {
   /**
    * The caught events {@link IDSProofListener#proofClosed(DSProofEvent)}.
    */
   private List<DSProofEvent> closedEvents = new LinkedList<DSProofEvent>();

   /**
    * The caught events {@link IDSProofListener#referencesChanged(DSProofEvent)}.
    */
   private List<DSProofEvent> referenceChangedEvents = new LinkedList<DSProofEvent>();
   
   /**
    * Returns all caught events {@link IDSProofListener#proofClosed(DSProofEvent)}.
    * @return The events.
    */
   public List<DSProofEvent> getClosedEvents() {
      return closedEvents;
   }

   /**
    * Returns all caught events {@link IDSProofListener#referencesChanged(DSProofEvent)}.
    * @return The events.
    */
   public List<DSProofEvent> getReferenceChangedEvents() {
      return referenceChangedEvents;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void proofClosed(DSProofEvent e) {
      closedEvents.add(e);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void referencesChanged(DSProofEvent e) {
      referenceChangedEvents.add(e);
   }
}