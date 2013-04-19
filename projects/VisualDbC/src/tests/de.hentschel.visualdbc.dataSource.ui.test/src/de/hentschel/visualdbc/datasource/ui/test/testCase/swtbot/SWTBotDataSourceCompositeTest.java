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

package de.hentschel.visualdbc.datasource.ui.test.testCase.swtbot;

import java.util.Map;

import junit.framework.TestCase;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCombo;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.Test;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.ui.composite.DataSourceComposite;
import de.hentschel.visualdbc.datasource.ui.test.dataSource.UIDummyDriverA;
import de.hentschel.visualdbc.datasource.ui.test.dataSource.UIDummyDriverB;
import de.hentschel.visualdbc.datasource.ui.test.util.PropertyChangeLogger;
import de.hentschel.visualdbc.datasource.ui.test.util.TestDataSourceUIUtil;
import de.hentschel.visualdbc.datasource.util.DriverUtil;

/**
 * SWT Bot tests for {@link DataSourceComposite}
 * @author Martin Hentschel
 */
public class SWTBotDataSourceCompositeTest extends TestCase {
   /**
    * Tests getting and setting values by API and user.
    */
   @Test
   public void testGettingAndSettingValues_InvalidInitialized() {
      doTest(false);
   }

   /**
    * Tests getting and setting values by API and user.
    */
   @Test
   public void testGettingAndSettingValues_ValidInitialized() {
      doTest(true);
   }
   
   /**
    * Executes the test.
    * @param initializeWithValidValues {@code true} = valid values, {@code false} one invalid value.
    */
   protected void doTest(boolean initializeWithValidValues) {
      // Get drivers
      UIDummyDriverA.setInitializeValidSettings(initializeWithValidValues);
      UIDummyDriverA driverA = (UIDummyDriverA)DriverUtil.getDriver(UIDummyDriverA.class.getCanonicalName());
      assertNotNull(driverA);
      UIDummyDriverB driverB = (UIDummyDriverB)DriverUtil.getDriver(UIDummyDriverB.class.getCanonicalName());
      assertNotNull(driverB);
      // Create test project
      IProject project;
      if (!ResourcesPlugin.getWorkspace().getRoot().getProject("SWTBotDataSourceCompositeTest").exists()) {
         project = TestUtilsUtil.createProject("SWTBotDataSourceCompositeTest");
      }
      else {
         project = ResourcesPlugin.getWorkspace().getRoot().getProject("SWTBotDataSourceCompositeTest");
      }
      final IStructuredSelection selection = SWTUtil.createSelection(project);
      // Create shell and UI control instance and set initial value
      IRunnableWithResult<DataSourceComposite> createRun = new AbstractRunnableWithResult<DataSourceComposite>() {
         @Override
         public void run() {
            Shell shell = new Shell(Display.getDefault());
            shell.setText("SWTBotDataSourceCompositeTest");
            shell.setLayout(new FillLayout());
            shell.setSize(500, 300);
            DataSourceComposite control = new DataSourceComposite(shell, SWT.NONE, selection);
            setResult(control);
            shell.open();
         }
      };
      Display.getDefault().syncExec(createRun);
      final DataSourceComposite control = createRun.getResult();
      assertNotNull(control);
      // Add event logger
      PropertyChangeLogger driverLogger = new PropertyChangeLogger();
      control.addPropertyChangeListener(DataSourceComposite.PROP_DRIVER, driverLogger);
      assertEquals(1, control.getPropertyChangeListeners(DataSourceComposite.PROP_DRIVER).length);
      assertEquals(driverLogger, control.getPropertyChangeListeners(DataSourceComposite.PROP_DRIVER)[0]);
      PropertyChangeLogger valuesLogger = new PropertyChangeLogger();
      control.addPropertyChangeListener(DataSourceComposite.PROP_VALUES, valuesLogger);
      assertEquals(1, control.getPropertyChangeListeners(DataSourceComposite.PROP_VALUES).length);
      assertEquals(valuesLogger, control.getPropertyChangeListeners(DataSourceComposite.PROP_VALUES)[0]);
      // Create bot and get Shell
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotShell botShell = bot.shell("SWTBotDataSourceCompositeTest");
      SWTBotCombo driverCombo = botShell.bot().comboBox();
      // Test initial values
      if (!initializeWithValidValues) {
         compareValuesByApi(control, driverA, "Resource Package: No existing project or folder defined.", Boolean.TRUE, new Path(""));
         compareValuesByUser(driverCombo, botShell, driverA, driverA.getBooleanLabelName(), true, true, false, false, "");
         // Select valid resource
         botShell.bot().text().setText(project.getFullPath().toString()); // Throws no event...
         botShell.bot().radio(0).click();
         compareEvents(control, driverLogger, valuesLogger, null, Boolean.TRUE, project.getFullPath());
      }
      compareValuesByApi(control, driverA, null, Boolean.TRUE, project.getFullPath());
      compareValuesByUser(driverCombo, botShell, driverA, driverA.getBooleanLabelName(), true, true, false, false, project.getFullPath().toString());
      // Select driver b (switch from valid to valid settings)
      driverCombo.setSelection(driverB.getName());
      compareEvents(control, driverLogger, valuesLogger, driverB, null, null);
      compareValuesByApi(control, driverB, null, Boolean.FALSE, project.getFullPath());
      compareValuesByUser(driverCombo, botShell, driverB, driverB.getBooleanLabelName(), false, true, false, false, project.getFullPath().toString());
      // Select file
      botShell.bot().radio(1).click();
      compareEvents(control, driverLogger, valuesLogger, null, Boolean.FALSE, ResourceUtil.getLocation(project));
      compareValuesByApi(control, driverB, null, Boolean.FALSE, ResourceUtil.getLocation(project));
      compareValuesByUser(driverCombo, botShell, driverB, driverB.getBooleanLabelName(), false, false, true, false, ResourceUtil.getLocation(project).toString());
      // Select invalid package
      botShell.bot().radio(2).click();
      compareEvents(control, driverLogger, valuesLogger, null, Boolean.FALSE, null);
      compareValuesByApi(control, driverB, "Resource Package: No directory defined.", Boolean.FALSE, null);
      compareValuesByUser(driverCombo, botShell, driverB, driverB.getBooleanLabelName(), false, false, false, true, "");
      // Select driver a (switch from invalid to valid)
      driverCombo.setSelection(driverA.getName());
      compareEvents(control, driverLogger, valuesLogger, driverA, null, null);
      compareValuesByApi(control, driverA, null, Boolean.TRUE, project.getFullPath());
      compareValuesByUser(driverCombo, botShell, driverA, driverA.getBooleanLabelName(), true, true, false, false, project.getFullPath().toString());
      // Select driver b (switch from valid to invalid)
      driverCombo.setSelection(driverB.getName());
      compareEvents(control, driverLogger, valuesLogger, driverB, null, null);
      compareValuesByApi(control, driverB, "Resource Package: No directory defined.", Boolean.FALSE, null);
      compareValuesByUser(driverCombo, botShell, driverB, driverB.getBooleanLabelName(), false, false, false, true, "");
      // Select driver a (switch from invalid to valid)
      driverCombo.setSelection(driverA.getName());
      compareEvents(control, driverLogger, valuesLogger, driverA, null, null);
      compareValuesByApi(control, driverA, null, Boolean.TRUE, project.getFullPath());
      compareValuesByUser(driverCombo, botShell, driverA, driverA.getBooleanLabelName(), true, true, false, false, project.getFullPath().toString());
      // Select invalid resource
      botShell.bot().text().setText("INVALID"); // Throws no event...
      botShell.bot().radio(0).click();
      compareEvents(control, driverLogger, valuesLogger, null, Boolean.TRUE, new Path("INVALID"));
      compareValuesByApi(control, driverA, "Resource Package: No existing project or folder defined.", Boolean.TRUE, new Path("INVALID"));
      compareValuesByUser(driverCombo, botShell, driverA, driverA.getBooleanLabelName(), true, true, false, false, "INVALID");
      // Select driver b (switch from invalid to invalid)
      driverCombo.setSelection(driverB.getName());
      compareEvents(control, driverLogger, valuesLogger, driverB, null, null);
      compareValuesByApi(control, driverB, "Resource Package: No directory defined.", Boolean.FALSE, null);
      compareValuesByUser(driverCombo, botShell, driverB, driverB.getBooleanLabelName(), false, false, false, true, "");
      // Remove event logger
      control.removePropertyChangeListener(DataSourceComposite.PROP_DRIVER, driverLogger);
      assertEquals(0, control.getPropertyChangeListeners(DataSourceComposite.PROP_DRIVER).length);
      control.removePropertyChangeListener(DataSourceComposite.PROP_VALUES, valuesLogger);
      assertEquals(0, control.getPropertyChangeListeners(DataSourceComposite.PROP_VALUES).length);
      // Close shell
      control.getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            control.getShell().close();
         }
      });
   }
   
   /**
    * Compares the events.
    * @param control The {@link DataSourceComposite}.
    * @param driverLogger The driver logger.
    * @param valuesLogger The values logger.
    * @param expectedDriver The expected driver or {@code null} if no event is expected.
    * @param expectedBoolean The expected boolean value or {@code null} if no event is expected.
    * @param expectedPackage The expected package value or {@code null} if no event is expected.
    */
   protected void compareEvents(DataSourceComposite control, 
                                PropertyChangeLogger driverLogger, 
                                PropertyChangeLogger valuesLogger, 
                                IDSDriver expectedDriver,
                                Boolean expectedBoolean,
                                Object expectedPackage) {
      // Compare driver event
      if (expectedDriver != null) {
         assertEquals(1, driverLogger.getLog().size());
         assertNotNull(driverLogger.getLog().get(0));
         assertEquals(expectedDriver, driverLogger.getLog().get(0).getNewValue());
         assertEquals(DataSourceComposite.PROP_DRIVER, driverLogger.getLog().get(0).getPropertyName());
         assertEquals(control, driverLogger.getLog().get(0).getSource());
         driverLogger.clear();
      }
      else {
         assertEquals(0, driverLogger.getLog().size());
      }
      // Compare values event
      if (expectedBoolean != null || expectedPackage != null) {
         assertEquals(1, valuesLogger.getLog().size());
         assertNotNull(valuesLogger.getLog().get(0));
         assertTrue(valuesLogger.getLog().get(0).getNewValue() instanceof Map);
         Map<?, ?> values = (Map<?, ?>)valuesLogger.getLog().get(0).getNewValue();
         assertEquals(2, values.size());
         assertEquals(expectedBoolean, values.get(UIDummyDriverA.SETTING_BOOLEAN));
         assertEquals(expectedPackage, values.get(UIDummyDriverA.SETTING_RESOURCE_PACKAGE));
         assertEquals(DataSourceComposite.PROP_VALUES, valuesLogger.getLog().get(0).getPropertyName());
         assertEquals(control, valuesLogger.getLog().get(0).getSource());
         valuesLogger.clear();
      }
      else {
         assertEquals(0, valuesLogger.getLog().size());
      }
   }

   /**
    * Compares the current values by user.
    * @param driverCombo The driver bot Combo.
    * @param botShell The bot Shell to use.
    * @param expectedDriver The expected driver.
    * @param expectedFirstLabelText The expected text of the first setting label.
    * @param expectedBooleanSelection The expected boolean selection.
    * @param expectedResourceSelection The expected resource selection.
    * @param expectedDirectorySelection The expected directory selection.
    * @param expectedPackageselection The expected package selection.
    * @param expectedPath The expected path value.
    */
   protected void compareValuesByUser(SWTBotCombo driverCombo,
                                      SWTBotShell botShell,
                                      IDSDriver expectedDriver,
                                      String expectedFirstLabelText,
                                      boolean expectedBooleanSelection,
                                      boolean expectedResourceSelection,
                                      boolean expectedDirectorySelection,
                                      boolean expectedPackageselection,
                                      String expectedPath) {
      assertEquals(expectedDriver.getName(), driverCombo.getText());
      assertEquals(expectedFirstLabelText, botShell.bot().label(1).getText());
      assertEquals(expectedBooleanSelection, botShell.bot().checkBox().isChecked());
      assertEquals(expectedResourceSelection, botShell.bot().radio(0).isSelected());
      assertEquals(expectedDirectorySelection, botShell.bot().radio(1).isSelected());
      assertEquals(expectedPackageselection, botShell.bot().radio(2).isSelected());
      assertEquals(expectedPath, botShell.bot().text().getText());
   }

   /**
    * Compares the current values by API.
    * @param control The {@link DataSourceComposite} to use.
    * @param expectedDriver The expected {@link IDSDriver}.
    * @param expectedBooleanValue The expected boolean value.
    * @param expectedPackageValue The expected package value.
    */
   protected void compareValuesByApi(DataSourceComposite control,
                                     IDSDriver expectedDriver,
                                     String expectedgetSettingsValidationMessage,
                                     Boolean expectedBooleanValue,
                                     Object expectedPackageValue) {
      assertEquals(expectedgetSettingsValidationMessage, TestDataSourceUIUtil.getSettingsValidationMessageThreadSave(control));
      assertEquals(expectedDriver, TestDataSourceUIUtil.getDriverThreadSave(control));
      Map<String, Object> values = TestDataSourceUIUtil.getValuesThreadSave(control);
      assertEquals(2, values.size());
      assertEquals(expectedBooleanValue, values.get(UIDummyDriverA.SETTING_BOOLEAN));
      assertEquals(expectedPackageValue, values.get(UIDummyDriverA.SETTING_RESOURCE_PACKAGE));
   }
}