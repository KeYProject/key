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

import de.hentschel.visualdbc.datasource.model.IDSProof;

/**
 * Listens for changes on an {@link IDSProof}.
 * @author Martin Hentschel
 */
public interface IDSProofListener extends EventListener {
   /**
    * When a proof was closed.
    * @param e The thrown event.
    */
   public void proofClosed(DSProofEvent e);
   
   /**
    * When new proof references were added or old references removed.
    * @param e The thrown event.
    */
   public void referencesChanged(DSProofEvent e);
}
