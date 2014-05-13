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
import de.hentschel.visualdbc.interactive.proving.ui.util.FinderUtil;

/**
 * <p>
 * Instantiates {@link IDSFinder} if it can handle a given {@link IDSConnection}.
 * </p>
 * <p>
 * Possible factories are registered via extension point {@link FinderUtil#DS_FINDER_EXTENSION_POINT}.
 * The class {@link FinderUtil} provides static methods to find the correct
 * {@link IDSFinderFactory} for a given {@link IDSConnection} respecting the priority.
 * </p>
 * <p>
 * The default {@link IDSFinderFactory} {@link DefaultDSFinderFactory} handles all
 * {@link IDSConnection} via the {@link DefaultDSFinder} if they are not {@code null}.
 * </p>
 * @author Martin Hentschel
 * @see IDSFinder
 * @see AbstractDSFinder
 * @see DefaultDSFinderFactory
 * @see DefaultDSFinder
 */
public interface IDSFinderFactory {
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
    * Creates an {@link IDSFinder} instance that works with the given
    * {@link IDSConnection}.
    * @param connection The {@link IDSConnection} to use.
    * @return The created {@link IDSFinder}.
    */
   public IDSFinder createFinder(IDSConnection connection);
}