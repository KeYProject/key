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
import de.hentschel.visualdbc.dbcmodel.DbcModel;

/**
 * Provides a basic implementation of {@link IDbcFinder}.
 * @author Martin Hentschel
 */
public abstract class AbstractDbcFinder implements IDbcFinder {
   /**
    * The used {@link IDSConnection}.
    */
   private DbcModel model;

   /**
    * Constructor.
    * @param model The {@link DbcModel} to use.
    */
   public AbstractDbcFinder(DbcModel model) {
      super();
      Assert.isNotNull(model);
      this.model = model;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public DbcModel getModel() {
      return model;
   }
}