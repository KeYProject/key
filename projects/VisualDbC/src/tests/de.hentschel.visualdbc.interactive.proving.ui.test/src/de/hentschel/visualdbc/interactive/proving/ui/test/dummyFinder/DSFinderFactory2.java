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

package de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinderFactory;

public class DSFinderFactory2 implements IDSFinderFactory {
   @Override
   public int getPriority() {
      return 2;
   }

   @Override
   public boolean canHandle(IDSConnection connection) {
      return false;
   }

   @Override
   public IDSFinder createFinder(IDSConnection connection) {
      return null;
   }
}
