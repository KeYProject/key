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

package de.hentschel.visualdbc.generation.ui.test.testCase.swtbot;

import java.util.Map;

import junit.framework.TestCase;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.Before;
import org.junit.Test;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.ui.test.dataSource.UIDummyDriver1;
import de.hentschel.visualdbc.datasource.ui.test.dataSource.UIDummyDriverA;
import de.hentschel.visualdbc.datasource.util.DriverUtil;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.generation.ui.test.util.ISWTBotShellManipulator;
import de.hentschel.visualdbc.generation.ui.test.util.TestGenerationUIUtil;
import de.hentschel.visualdbc.generation.ui.wizard.GenerateDiagramWizard;

/**
 * SWT Bot tests for {@link GenerateDiagramWizard}.
 * @author Martin Hentschel
 */
public class SWTBotGenerateDiagramWizardTest extends TestCase {
   /**
    *  The {@link SWTWorkbenchBot} to use.
    */
   private SWTWorkbenchBot bot;
   
   /**
    * {@inheritDoc}
    */
   @Before
   @Override
   public void setUp() throws Exception {
      super.setUp();
      bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
   }
   
   /**
    * Tests manipulating the driver settings
    */
   @Test
   public void testManipulateDriverSettings() {
      try {
         // Create project structure
         IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotGenerateDiagramWizardTest_testManipulateDriverSettings");
         // Select project in project explorer
         TestUtilsUtil.selectInProjectExplorer(bot, javaProject.getProject().getName());
         // Get driver and open expected connection
         IDSDriver driver = DriverUtil.getDriver(UIDummyDriver1.class.getCanonicalName());
         assertNotNull(driver);
         IDSConnection connection = driver.createConnection();
         Map<String, Object> settings = TestGenerationUtil.createDefaultSettings(driver, SWTUtil.createSelection(javaProject.getPath()));
         settings.put(UIDummyDriver1.SETTING_BOOLEAN, Boolean.FALSE);
         settings.put(UIDummyDriver1.SETTING_PACKAGE, ResourceUtil.getLocation(javaProject.getProject()));
         connection.connect(settings, false, null);
         // Open new wizard
         ISWTBotShellManipulator manipulator = new ISWTBotShellManipulator() {
            @Override
            public void manipulate(SWTBotShell shell) {
               SWTBotButton finishButton = shell.bot().button("Finish");
               assertTrue(finishButton.isEnabled());
               // Unselect boolean value
               shell.bot().checkBox().deselect();
               assertTrue(finishButton.isEnabled());
               // Select invalid path
               shell.bot().text().setText("INVALID");
               assertFalse(finishButton.isEnabled());
               // Select valid file
               shell.bot().radio(1).click();
               assertTrue(finishButton.isEnabled());
            }
         };
         TestGenerationUIUtil.createDiagramViaGenerateDiagramWizard(bot, 
                                                                    true,
                                                                    javaProject.getProject().getFolder("src"),
                                                                    "Test.dbc_diagram", 
                                                                    javaProject.getProject().getFolder("src"),
                                                                    "Test.dbc",
                                                                    driver,
                                                                    manipulator,
                                                                    true,
                                                                    connection);
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }   

   /**
    * Tests initial driver with invalid settings.
    */
   @Test
   public void testNoEarlyFinish() {
      try {
         UIDummyDriverA.setInitializeValidSettings(false);
         doTestDefaultValues("SWTBotGenerateDiagramWizardTest_testNoEarlyFinish", false, true);
      }
      finally {
         UIDummyDriverA.setInitializeValidSettings(true);
      }
   }

   /**
    * Tests finishing the wizard with default values.
    */
   @Test
   public void testDefaultValues_Finish() {
      doTestDefaultValues("SWTBotGenerateDiagramWizardTest_testDefaultValues_Finish", true, true);
   }

   /**
    * Tests canceling the wizard with default values.
    */
   @Test
   public void testDefaultValues_Cancel() {
      doTestDefaultValues("SWTBotGenerateDiagramWizardTest_testDefaultValues_Cancel", true, false);
   }
   
   /**
    * Executes a test with default settings.
    * @param projectName The project name.
    * @param earlyFinishAllowed Early finish allowed?
    * @param finish Finish or cancel wizard. 
    */
   protected void doTestDefaultValues(String projectName, boolean earlyFinishAllowed, boolean finish) {
      try {
         // Create project structure
         IJavaProject javaProject = TestUtilsUtil.createJavaProject(projectName);
         // Select project in project explorer
         TestUtilsUtil.selectInProjectExplorer(bot, javaProject.getProject().getName());
         // Get driver and open expected connection
         IDSDriver driver = DriverUtil.getDriver(UIDummyDriver1.class.getCanonicalName());
         assertNotNull(driver);
         IDSConnection connection = driver.createConnection();
         Map<String, Object> settings = TestGenerationUtil.createDefaultSettings(driver, SWTUtil.createSelection(javaProject.getPath()));
         connection.connect(settings, false, null);
         // Open new wizard
         TestGenerationUIUtil.createDiagramViaGenerateDiagramWizard(bot, 
                                                                    earlyFinishAllowed,
                                                                    javaProject.getProject().getFolder("src"),
                                                                    "Test.dbc_diagram", 
                                                                    javaProject.getProject().getFolder("src"),
                                                                    "Test.dbc",
                                                                    driver,
                                                                    null,
                                                                    finish,
                                                                    connection);
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
}