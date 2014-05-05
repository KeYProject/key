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
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.interactive.proving.ui.util.FinderUtil;

/**
 * <p>
 * Instantiates {@link IDbcFinder} if it can handle a given {@link IDSConnection}.
 * </p>
 * <p>
 * Possible factories are registered via extension point {@link FinderUtil#DBC_FINDER_EXTENSION_POINT}.
 * The class {@link FinderUtil} provides static methods to find the correct
 * {@link IDbcFinderFactory} for a given {@link IDSConnection} respecting the priority.
 * </p>
 * <p>
 * The default {@link IDbcFinderFactory} {@link DefaultDbcFinderFactory} handles all
 * {@link IDSConnection} via the {@link DefaultDbcFinder} if they are not {@code null}.
 * </p>
 * @author Martin Hentschel
 * @see IDbcFinder
 * @see AbstractDbcFinder
 * @see DefaultDbcFinderFactory
 * @see DefaultDbcFinder
 */
public interface IDbcFinderFactory {
   /**
    * The priority.
    * @return The priority.
    */
   public int getPriority();
   
   /**
    * Checks if this factory can handle the given {@link IDSConnection}.
    * @param connection The {@link IDSConnection} to check.
    * @return {@code true} = can handle, {@code false} = can't handle.
    */
   public boolean canHandle(IDSConnection connection);
   
   /**
    * Creates an {@link IDbcFinder} instance that works with the given
    * {@link DbcModel}.
    * @param model The {@link DbcModel} to search in.
    * @return The created {@link IDbcFinder}.
    */
   public IDbcFinder createFinder(DbcModel model);
}