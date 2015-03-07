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

package de.hentschel.visualdbc.datasource.key.test.testCase.swtbot.example;

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.swtbot.swing.bot.SwingBot;
import org.key_project.swtbot.swing.bot.SwingBotJButton;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.key.test.Activator;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * This is an example that shows the usage of SwingBot by closing
 * an opened proof automatically in KeY.
 * @author Martin Hentschel
 */
public class SWTBotExampeForSwingBot extends AbstractSetupTestCase {
   /**
    * Opens the proof obligation "PreservesOwnInv" of method
    * paycard.PayCard#isValid() and closes it automatically.
    * @throws CoreException Occurred Exception
    * @throws DSException Occurred Exception
    * @throws DSCanceledException Occurred Exception
    */
   @Test
   public void testCloseProof() throws Exception {
      IDSConnection connection = null;
      try {
         // Create project and fill it with java files from KeY Quicktour
         IProject project = TestUtilsUtil.createProject("SWTBotForSwing");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/quicktour/test/paycard", project);
         File location = ResourceUtil.getLocation(project); 
         // Open data source connection to KeY in interactive modus
         connection = TestKeyUtil.createKeyConnection(true, location);
         // Get IDSProvable to open a proof
         IDSPackage paycardPackage = connection.getPackage("paycard");
         IDSClass paycardClass = paycardPackage.getClass("PayCard");
         IDSMethod method = paycardClass.getMethod("isValid()");
         // Open proof obligation "PreservesOwnInv"
         IDSProof proof = method.openInteractiveProof("PreservesOwnInv");
         // Get KeY main JFrame with Swing extension for SWTBot
         SwingBot bot = new SwingBot();
         SwingBotJFrame frame = bot.jFrame("KeY -- Prover: " + location);
         // Click on "start/stop" JButton to close the proof automatically
         SwingBotJButton button = frame.bot().jButtonWithTooltip("Start/stop automated proof search");
         button.clickAndWait();
         // Close opened result dialog
         SwingBotJDialog closeDiag = frame.bot().jDialog("Proof closed");
         closeDiag.bot().jButton("OK").clickAndWait();
         // Make sure that proof is closed in the data source instance
         assertTrue(proof.isClosed());
      } finally {
         if (connection != null) { connection.disconnect(); }
      }
   }
}