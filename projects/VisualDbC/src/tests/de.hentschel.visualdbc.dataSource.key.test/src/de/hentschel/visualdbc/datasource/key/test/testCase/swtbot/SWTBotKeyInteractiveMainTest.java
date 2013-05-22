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

package de.hentschel.visualdbc.datasource.key.test.testCase.swtbot;

import java.io.File;

import javax.swing.JFrame;

import junit.framework.TestCase;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;
import org.key_project.swtbot.swing.bot.finder.waits.Conditions;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

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
   public void testDisconnectingConnection() throws CoreException, DSException {
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
   public void testClosingFrameByUser() throws CoreException, DSException {
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