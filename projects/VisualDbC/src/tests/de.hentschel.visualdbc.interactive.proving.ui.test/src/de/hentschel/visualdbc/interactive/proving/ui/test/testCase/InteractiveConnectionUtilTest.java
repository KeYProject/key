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

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase;

import java.util.LinkedList;
import java.util.List;

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
import de.hentschel.visualdbc.interactive.proving.ui.util.event.IInteractiveConnectionUtilListener;
import de.hentschel.visualdbc.interactive.proving.ui.util.event.InteractiveConnectionUtilEvent;

/**
 * Tests for {@link InteractiveConnectionUtil}
 * @author Martin Hentschel
 */
public class InteractiveConnectionUtilTest extends TestCase {
   /**
    * Tests 
    * {@link InteractiveConnectionUtil#openConnection(DbcModel, org.eclipse.core.runtime.IProgressMonitor)},
    * {@link InteractiveConnectionUtil#isOpened(DbcModel)},
    * {@link InteractiveConnectionUtil#getConnection(DbcModel)} and
    * {@link InteractiveConnectionUtil#closeConnection(DbcModel)} together with the thrown events.
    */
   public void testOpeningAndClosingInteractiveConnections() throws DSException {
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
      LogListener listener = new LogListener();
      InteractiveConnectionUtil.addInteractiveConnectionUtilListener(listener);
      try {
         // Open separate connection that is always opened
         con2 = InteractiveConnectionUtil.openConnection(model2, null);
         assertNotNull(con2);
         assertConnected(con1, model1, false, con2, model2, true, listener, new InteractiveConnectionUtilEvent(con2, model2));
         // Open connection
         con1 = InteractiveConnectionUtil.openConnection(model1, null);
         assertNotNull(con1);
         assertConnected(con1, model1, true, con2, model2, true, listener, new InteractiveConnectionUtilEvent(con1, model1));
         // Get connection again
         IDSConnection conAgain = InteractiveConnectionUtil.openConnection(model1, null);
         assertSame(con1, conAgain);
         assertConnected(con1, model1, true, con2, model2, true, listener, null);
         // Close connection manually
         con1.disconnect();
         assertConnected(con1, model1, false, con2, model2, true, listener, null);
         // Close connection manually again
         con1.disconnect();
         assertConnected(con1, model1, false, con2, model2, true, listener, null);
         // Open connection second time
         con1 = InteractiveConnectionUtil.openConnection(model1, null);
         assertNotSame(con1, conAgain);
         assertConnected(con1, model1, true, con2, model2, true, listener, new InteractiveConnectionUtilEvent(con1, model1));
         // Get connection again
         conAgain = InteractiveConnectionUtil.openConnection(model1, null);
         assertSame(con1, conAgain);
         assertConnected(con1, model1, true, con2, model2, true, listener, null);
         // Close connection manually
         InteractiveConnectionUtil.closeConnection(model1);
         assertConnected(con1, model1, false, con2, model2, true, listener, null);
         // Close connection again
         con1.disconnect();
         assertConnected(con1, model1, false, con2, model2, true, listener, null);
         // Close second connection
         con2.disconnect();
         assertConnected(con1, model1, false, con2, model2, false, listener, null);
      }
      finally {
         InteractiveConnectionUtil.removeInteractiveConnectionUtilListener(listener);
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
   
   /**
    * Makes sure that the {@link IDSConnection} are in the given state.
    * @param con1 The first {@link IDSConnection}.
    * @param model1 The first {@link DbcModel}.
    * @param con1Connected Is first {@link IDSConnection} connected?
    * @param con2 The second {@link IDSConnection}.
    * @param model2 The second {@link DbcModel}.
    * @param con2Connected Is second {@link IDSConnection} connected?
    * @param listener The used {@link LogListener}.
    * @param expectedOpenEvent The expected event or {@code null} if no event is expected..
    * @throws DSException Occurred Exception.
    */
   protected void assertConnected(IDSConnection con1, 
                                  DbcModel model1, 
                                  boolean con1Connected,
                                  IDSConnection con2, 
                                  DbcModel model2, 
                                  boolean con2Connected,
                                  LogListener listener,
                                  InteractiveConnectionUtilEvent expectedOpenEvent) throws DSException {
      // Connection 1
      if (con1 != null) {
         assertEquals(con1Connected, con1.isConnected());
         assertEquals(con1Connected, InteractiveConnectionUtil.isOpened(model1));
         if (con1Connected) {
            assertEquals(con1, InteractiveConnectionUtil.getConnection(model1));
         }
         else {
            assertNull(InteractiveConnectionUtil.getConnection(model1));
         }
      }
      else {
         assertFalse(InteractiveConnectionUtil.isOpened(model1));
         assertNull(InteractiveConnectionUtil.getConnection(model1));
      }
      // Connection 2
      if (con2 != null) {
         assertEquals(con2Connected, con2.isConnected());
         assertEquals(con2Connected, InteractiveConnectionUtil.isOpened(model2));
         if (con2Connected) {
            assertEquals(con2, InteractiveConnectionUtil.getConnection(model2));
         }
         else {
            assertNull(InteractiveConnectionUtil.getConnection(model2));
         }
      }
      else {
         assertFalse(InteractiveConnectionUtil.isOpened(model2));
         assertNull(InteractiveConnectionUtil.getConnection(model2));
      }
      // Events
      listener.assertEvents(expectedOpenEvent);
   }
   
   /**
    * A logging {@link IInteractiveConnectionUtilListener}.
    * @author Martin Hentschel
    */
   private static final class LogListener implements IInteractiveConnectionUtilListener {
      /**
       * The caught open events.
       */
      private List<InteractiveConnectionUtilEvent> openEvents = new LinkedList<InteractiveConnectionUtilEvent>();

      /**
       * {@inheritDoc}
       */
      @Override
      public void connectionOpened(InteractiveConnectionUtilEvent e) {
         openEvents.add(e);
      }
      
      /**
       * Makes sure that the given {@link InteractiveConnectionUtilEvent} was thrown.
       * @param expectedOpenEvent The expected event or {@code null} if no event is expected..
       */
      protected void assertEvents(InteractiveConnectionUtilEvent expectedOpenEvent) {
         if (expectedOpenEvent != null) {
            assertEquals(1, openEvents.size());
            InteractiveConnectionUtilEvent current = openEvents.get(0);
            assertEquals(current.getConnection(), expectedOpenEvent.getConnection());
            assertEquals(current.getModel(), expectedOpenEvent.getModel());
            assertEquals(current.getSource(), expectedOpenEvent.getSource());
            openEvents.clear();
         }
         else {
            assertEquals(0, openEvents.size());
         }
      }
   }
}