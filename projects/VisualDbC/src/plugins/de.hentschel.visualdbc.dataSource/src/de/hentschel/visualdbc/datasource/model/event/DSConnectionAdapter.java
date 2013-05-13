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

/**
 * Provides an implementation of {@link IDSConnectionListener} that does
 * nothing.
 * @author Martin Hentschel
 */
public class DSConnectionAdapter implements IDSConnectionListener {
   /**
    * {@inheritDoc}
    */
   @Override
   public void connected(DSConnectionEvent e) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnected(DSConnectionEvent e) {
   }
}