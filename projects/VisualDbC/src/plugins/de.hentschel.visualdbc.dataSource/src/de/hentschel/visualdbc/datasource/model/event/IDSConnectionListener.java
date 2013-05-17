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