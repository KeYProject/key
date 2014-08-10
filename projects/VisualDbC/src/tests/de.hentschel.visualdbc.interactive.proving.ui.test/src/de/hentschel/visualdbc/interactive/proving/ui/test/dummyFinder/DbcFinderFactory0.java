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

package de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.test.dummyModel.DummyModelDriver;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.interactive.proving.ui.finder.DefaultDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinderFactory;

public class DbcFinderFactory0 implements IDbcFinderFactory {
   @Override
   public int getPriority() {
      return 0;
   }

   @Override
   public boolean canHandle(IDSConnection connection) {
      return connection != null && 
             connection.getDriver() != null && 
             DummyModelDriver.class.equals(connection.getDriver().getClass());
   }

   @Override
   public IDbcFinder createFinder(DbcModel model) {
      return new Finder0(model);
   }
   
   public static class Finder0 extends DefaultDbcFinder {
      public Finder0(DbcModel model) {
         super(model);
      }
   }
}