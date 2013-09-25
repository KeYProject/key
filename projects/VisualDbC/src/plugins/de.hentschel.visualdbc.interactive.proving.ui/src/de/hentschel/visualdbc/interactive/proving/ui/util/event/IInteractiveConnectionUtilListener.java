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

package de.hentschel.visualdbc.interactive.proving.ui.util.event;

import java.util.EventListener;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveConnectionUtil;

/**
 * Observes changes of {@link InteractiveConnectionUtil}.
 * @author Martin Hentschel
 */
public interface IInteractiveConnectionUtilListener extends EventListener {
   /**
    * When a new {@link IDSConnection} was opened.
    * @param e The event.
    */
   public void connectionOpened(InteractiveConnectionUtilEvent e);
}