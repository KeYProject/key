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

package de.hentschel.visualdbc.datasource.key.test.testCase.swtbot;

import java.io.File;

import javax.swing.JFrame;

import junit.framework.TestCase;

import org.eclipse.core.resources.IProject;
import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.BundleUtil;
import org.key_project.key4eclipse.util.eclipse.ResourceUtil;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;
import org.key_project.swtbot.swing.bot.finder.waits.Conditions;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.test.Activator;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.test.util.ConnectionLogger;
import de.hentschel.visualdbc.datasource.test.util.TestDataSourceUtil;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.uka.ilkd.key.gui.MainWindow;

/**
 * Tests for the interactive mode of a {@link KeyConnection}.
 * @author Martin Hentschel
 */
public class SWTBotKeyInteractiveMainTest extends TestCase {
   /**
    * Makes sure that the {@link IDSConnection} closes the opened 
    * {@link MainWindow} {@link JFrame} when the connection is
    * disconnected.
    */
   @Test
   public void testDisconnectingConnection() {
      IDSConnection connection = null;
      ConnectionLogger logger = new ConnectionLogger();
      try {
         // Create project and fill it with test data
         IProject project = TestUtilsUtil.createProject("SWTBotInteractiveKeyMainTest_testDisconnectingConnection");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/quicktour/paycard", project);
         // Open connection
         File location = ResourceUtil.getLocation(project); 
         TestCase.assertNotNull(location);
         TestCase.assertTrue(location.exists() && location.isDirectory());
         connection = TestKeyUtil.createKeyConnection(true, location, DSPackageManagement.getDefault(), logger);
         TestCase.assertTrue(connection.isConnected());
         TestDataSourceUtil.compareConnectionEvents(connection, logger, true, false, false);
         // Get opened frame
         SwingBotJFrame frame = TestKeyUtil.getInteractiveKeyMain(project);
         // Close connection
         TestGenerationUtil.closeConnection(connection);
         TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, true);
         connection.removeConnectionListener(logger);
         TestCase.assertEquals(0, connection.getConnectionListeners().length);
         connection = null;
         // Make sure that the frame was closed
         frame.bot().waitUntil(Conditions.componentCloses(frame));
         assertFalse(frame.isOpen());
      }
      catch (Exception e) {
         e.printStackTrace();
         TestCase.fail(e.getMessage());
      }
      finally {
         try {
            if (connection != null && connection.isConnected()) {
               TestGenerationUtil.closeConnection(connection);
               TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, true);
               connection.removeConnectionListener(logger);
               TestCase.assertEquals(0, connection.getConnectionListeners().length);
            }
         }
         catch (DSException e) {
            e.printStackTrace();
            fail(e.getMessage());
         }
      }
   }
   
   /**
    * Makes sure that the {@link IDSConnection} automatically disconnects
    * and throws the correct event when the {@link MainWindow} is closed.
    */
   @Test
   public void testClosingFrameByUser() {
      IDSConnection connection = null;
      ConnectionLogger logger = new ConnectionLogger();
      try {
         // Create project and fill it with test data
         IProject project = TestUtilsUtil.createProject("SWTBotInteractiveKeyMainTest_testClosingEvent");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/quicktour/paycard", project);
         // Open connection
         File location = ResourceUtil.getLocation(project); 
         TestCase.assertNotNull(location);
         TestCase.assertTrue(location.exists() && location.isDirectory());
         connection = TestKeyUtil.createKeyConnection(true, location, DSPackageManagement.getDefault(), logger);
         TestCase.assertTrue(connection.isConnected());
         TestDataSourceUtil.compareConnectionEvents(connection, logger, true, false, false);
         // Close interactive frame
         SwingBotJFrame frame = TestKeyUtil.getInteractiveKeyMain(project);
         TestKeyUtil.closeKeyMain(frame);
         //Check connection and events
         TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, true);
         connection.removeConnectionListener(logger);
         TestCase.assertEquals(0, connection.getConnectionListeners().length);
         connection = null;
      }
      catch (Exception e) {
         e.printStackTrace();
         TestCase.fail(e.getMessage());
      }
      finally {
         try {
            if (connection != null && connection.isConnected()) {
               TestGenerationUtil.closeConnection(connection);
               TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, true);
               connection.removeConnectionListener(logger);
               TestCase.assertEquals(0, connection.getConnectionListeners().length);
            }
         }
         catch (DSException e) {
            e.printStackTrace();
            fail(e.getMessage());
         }
      }
   }
}
