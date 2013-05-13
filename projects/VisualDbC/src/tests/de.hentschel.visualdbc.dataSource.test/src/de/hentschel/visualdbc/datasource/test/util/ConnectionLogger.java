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

package de.hentschel.visualdbc.datasource.test.util;

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.event.DSConnectionEvent;
import de.hentschel.visualdbc.datasource.model.event.IDSConnectionListener;

/**
 * Logs all events in an {@link IDSConnection} into the main memory.
 * @author Martin Hentschel
 */
public class ConnectionLogger implements IDSConnectionListener {
   /**
    * All events from {@link #connected(DSConnectionEvent)}.
    */
   private List<DSConnectionEvent> connected = new LinkedList<DSConnectionEvent>();

   /**
    * All events from {@link #disconnected(DSConnectionEvent)}.
    */
   private List<DSConnectionEvent> disconnected = new LinkedList<DSConnectionEvent>();

   /**
    * {@inheritDoc}
    */
   @Override
   public void connected(DSConnectionEvent e) {
      connected.add(e);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnected(DSConnectionEvent e) {
      disconnected.add(e);
   }
   
   /**
    * Returns all {@link #connected(DSConnectionEvent)} events.
    * @return The events.
    */
   public List<DSConnectionEvent> getConnected() {
      return connected;
   }

   /**
    * Returns all {@link #disconnected(DSConnectionEvent)} events.
    * @return The events.
    */
   public List<DSConnectionEvent> getDisconnected() {
      return disconnected;
   }
}