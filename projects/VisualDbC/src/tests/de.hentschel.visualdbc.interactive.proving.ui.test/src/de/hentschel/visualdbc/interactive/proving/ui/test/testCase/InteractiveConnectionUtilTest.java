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

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase;

import junit.framework.TestCase;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.test.dummyModel.DummyModelDriver;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveConnectionUtil;

/**
 * Tests for {@link InteractiveConnectionUtil}
 * @author Martin Hentschel
 */
public class InteractiveConnectionUtilTest extends TestCase {
   /**
    * Tests 
    * {@link InteractiveConnectionUtil#openConnection(DbcModel, org.eclipse.core.runtime.IProgressMonitor)},
    * {@link InteractiveConnectionUtil#isOpened(DbcModel)} and
    * {@link InteractiveConnectionUtil#closeConnection(DbcModel)}
    */
   public void testOpeningAndClosingInteractiveConnections() {
      // Create dummy DbCModels
      ResourceSet rst = new ResourceSetImpl();
      Resource resource1 = rst.createResource(URI.createFileURI("notExisting.xml"));
      DbcModel model1 = DbcmodelFactory.eINSTANCE.createDbcModel();
      resource1.getContents().add(model1);
      model1.setDriverId(DummyModelDriver.ID);
      Resource resource2 = rst.createResource(URI.createFileURI("notExisting2.xml"));
      DbcModel model2 = DbcmodelFactory.eINSTANCE.createDbcModel();
      resource2.getContents().add(model2);
      model2.setDriverId(DummyModelDriver.ID);
      // Test connection management
      IDSConnection con1 = null;
      IDSConnection con2 = null;
      try {
         // Open separate connection that is always opened
         con2 = InteractiveConnectionUtil.openConnection(model2, null);
         assertNotNull(con2);
         assertTrue(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model2));
         // Open connection
         con1 = InteractiveConnectionUtil.openConnection(model1, null);
         assertNotNull(con1);
         assertTrue(con1.isConnected());
         assertTrue(con1.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model1));
         assertTrue(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model2));
         // Get connection again
         IDSConnection conAgain = InteractiveConnectionUtil.openConnection(model1, null);
         assertSame(con1, conAgain);
         assertTrue(con1.isConnected());
         assertTrue(con1.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model1));
         assertTrue(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model2));
         // Close connection manually
         con1.disconnect();
         assertFalse(con1.isConnected());
         assertTrue(con1.isInteractive());
         assertFalse(InteractiveConnectionUtil.isOpened(model1));
         assertTrue(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model2));
         // Close connection manually again
         con1.disconnect();
         assertFalse(con1.isConnected());
         assertTrue(con1.isInteractive());
         assertFalse(InteractiveConnectionUtil.isOpened(model1));
         assertTrue(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model2));
         // Open connection second time
         con1 = InteractiveConnectionUtil.openConnection(model1, null);
         assertNotSame(con1, conAgain);
         assertTrue(con1.isConnected());
         assertTrue(con1.isInteractive());
         assertFalse(conAgain.isConnected());
         assertTrue(conAgain.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model1));
         assertTrue(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model2));
         // Get connection again
         conAgain = InteractiveConnectionUtil.openConnection(model1, null);
         assertSame(con1, conAgain);
         assertTrue(con1.isConnected());
         assertTrue(con1.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model1));
         assertTrue(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model2));
         // Close connection manually
         InteractiveConnectionUtil.closeConnection(model1);
         assertFalse(con1.isConnected());
         assertTrue(con1.isInteractive());
         assertFalse(InteractiveConnectionUtil.isOpened(model1));
         assertTrue(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model2));
         // Close connection again
         con1.disconnect();
         assertFalse(con1.isConnected());
         assertTrue(con1.isInteractive());
         assertFalse(InteractiveConnectionUtil.isOpened(model1));
         assertTrue(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertTrue(InteractiveConnectionUtil.isOpened(model2));
         // Close second connection
         con2.disconnect();
         assertFalse(con2.isConnected());
         assertTrue(con2.isInteractive());
         assertFalse(InteractiveConnectionUtil.isOpened(model2));
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      finally {
         try {
            if (con1 != null && con1.isConnected()) {
               InteractiveConnectionUtil.closeConnection(model1);
            }
            if (con2 != null && con2.isConnected()) {
               InteractiveConnectionUtil.closeConnection(model2);
            }
         }
         catch (DSException e) {
            e.printStackTrace();
            fail(e.getMessage());
         }
      }
   }
}
