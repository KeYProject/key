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

package de.hentschel.visualdbc.interactive.proving.ui.finder;

import de.hentschel.visualdbc.datasource.model.IDSConnection;

/**
 * Returns the default {@link IDSFinderFactory} that is used if no special
 * {@link IDSFinderFactory} is implemented for an {@link IDSConnection}.
 * @author Martin Hentschel
 */
public class DefaultDSFinderFactory implements IDSFinderFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public int getPriority() {
      return Integer.MIN_VALUE;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canHandle(IDSConnection connection) {
      return connection != null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSFinder createFinder(IDSConnection connection) {
      return new DefaultDSFinder(connection);
   }
}