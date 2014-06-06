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

package de.hentschel.visualdbc.datasource.model.implementation;

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.event.DSConnectionEvent;
import de.hentschel.visualdbc.datasource.model.event.IDSConnectionListener;

/**
 * Provides a basic implementation of {@link IDSConnection}.
 * @author Martin Hentschel
 */
public abstract class AbstractDSConnection extends AbstractDSContainer implements IDSConnection {
   /**
    * Contains all listeners.
    */
   private List<IDSConnectionListener> listeners = new LinkedList<IDSConnectionListener>();

   /**
    * {@inheritDoc}
    */
   @Override
   public void addConnectionListener(IDSConnectionListener l) {
      if (l != null) {
         listeners.add(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeConnectionListener(IDSConnectionListener l) {
      if (l != null) {
         listeners.remove(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSConnectionListener[] getConnectionListeners() {
      return listeners.toArray(new IDSConnectionListener[listeners.size()]);
   }
   
   /**
    * Fires the event {@link IDSConnectionListener#connected(DSConnectionEvent)} 
    * to all listeners.
    * @param e The event to fire.
    */
   protected void fireConnected(DSConnectionEvent e) {
      IDSConnectionListener[] allListener = getConnectionListeners();
      for (IDSConnectionListener listener : allListener) {
         listener.connected(e);
      }
   }
   
   /**
    * Fires the event {@link IDSConnectionListener#disconnected(DSConnectionEvent)} 
    * to all listeners.
    * @param e The event to fire.
    */
   protected void fireDisconnected(DSConnectionEvent e) {
      IDSConnectionListener[] allListener = getConnectionListeners();
      for (IDSConnectionListener listener : allListener) {
         listener.disconnected(e);
      }
   }
}