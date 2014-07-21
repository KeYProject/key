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

import org.eclipse.core.runtime.Assert;

import de.hentschel.visualdbc.datasource.model.IDSConnection;

/**
 * Provides a basic implementation of {@link IDSFinder}.
 * @author Martin Hentschel
 */
public abstract class AbstractDSFinder implements IDSFinder {
   /**
    * The used {@link IDSConnection}.
    */
   private IDSConnection connection;

   /**
    * Constructor.
    * @param connection The {@link IDSConnection} to use.
    */
   public AbstractDSFinder(IDSConnection connection) {
      super();
      Assert.isNotNull(connection);
      this.connection = connection;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSConnection getConnection() {
      return connection;
   }
}