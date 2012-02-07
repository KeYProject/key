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

package de.hentschel.visualdbc.datasource.model.event;

import java.util.EventListener;

import de.hentschel.visualdbc.datasource.model.IDSConnection;

/**
 * Listens for connection changes on an {@link IDSConnection}.
 * @author Martin Hentschel
 */
public interface IDSConnectionListener extends EventListener {
   /**
    * When a connection was established.
    * @param e The event.
    */
   public void connected(DSConnectionEvent e);
   
   /**
    * When a connection was closed.
    * @param e The event.
    */
   public void disconnected(DSConnectionEvent e);
}
