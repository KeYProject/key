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

package de.hentschel.visualdbc.interactive.proving.ui.finder;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.dbcmodel.DbcModel;

/**
 * Returns the default {@link IDbcFinderFactory} that is used if no special
 * {@link IDbcFinderFactory} is implemented for an {@link IDSConnection}.
 * @author Martin Hentschel
 */
public class DefaultDbcFinderFactory implements IDbcFinderFactory {
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
   public IDbcFinder createFinder(DbcModel model) {
      return new DefaultDbcFinder(model);
   }
}