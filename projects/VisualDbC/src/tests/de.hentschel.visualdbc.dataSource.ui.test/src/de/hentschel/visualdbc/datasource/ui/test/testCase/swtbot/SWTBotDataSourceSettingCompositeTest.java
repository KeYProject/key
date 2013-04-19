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

import java.util.List;
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
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCombo;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotRadio;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.Test;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.ui.composite.DataSourceSettingComposite;
import de.hentschel.visualdbc.datasource.ui.test.dataSource.UIDummyDriver1;
import de.hentschel.visualdbc.datasource.ui.test.util.DataSourceSettingCompositeLogger;
import de.hentschel.visualdbc.datasource.ui.test.util.TestDataSourceUIUtil;
import de.hentschel.visualdbc.datasource.util.DriverUtil;

/**
 * SWT Bot tests for {@link DataSourceSettingComposite}
 * @author Martin Hentschel
 */
public class SWTBotDataSourceSettingCompositeTest extends TestCase {
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
      // Get driver
      UIDummyDriver1.setInitializeValidSettings(initializeWithValidValues);
      IDSDriver driver = DriverUtil.getDriver(UIDummyDriver1.class.getCanonicalName());
      assertNotNull(driver);
      final List<IDSConnectionSetting> connectionSettings = driver.getConnectionSettings();
      assertNotNull(connectionSettings);
      assertEquals(4, connectionSettings.size());
      // Create test project
      IProject project;
      if (!ResourcesPlugin.getWorkspace().getRoot().getProject("SWTBotDataSourceSettingCompositeTest").exists()) {
         project = TestUtilsUtil.createProject("SWTBotDataSourceSettingCompositeTest");
      }
      else {
         project = ResourcesPlugin.getWorkspace().getRoot().getProject("SWTBotDataSourceSettingCompositeTest");
      }
      final IStructuredSelection selection = SWTUtil.createSelection(project);
      // Create shell and UI control instance and set initial value
      IRunnableWithResult<DataSourceSettingComposite> createRun = new AbstractRunnableWithResult<DataSourceSettingComposite>() {
         @Override
         public void run() {
            Shell shell = new Shell(Display.getDefault());
            shell.setText("SWTBotDataSourceSettingCompositeTest");
            shell.setLayout(new FillLayout());
            shell.setSize(500, 300);
            DataSourceSettingComposite control = new DataSourceSettingComposite(shell, SWT.NONE, connectionSettings, selection);
            setResult(control);
            shell.open();
         }
      };
      Display.getDefault().syncExec(createRun);
      final DataSourceSettingComposite control = createRun.getResult();
      assertNotNull(control);
      // Add event logger
      DataSourceSettingCompositeLogger logger = new DataSourceSettingCompositeLogger();
      control.addDataSourceSettingCompositeListener(logger);
      assertEquals(1, control.getDataSourceSettingCompositeListeners().length);
      assertEquals(logger, control.getDataSourceSettingCompositeListeners()[0]);
      // Create bot and get Shell
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotShell botShell = bot.shell("SWTBotDataSourceSettingCompositeTest");
      SWTBotCheckBox booleanBox = botShell.bot().checkBox();
      SWTBotCombo packageCombo = botShell.bot().comboBox();
      SWTBotRadio resource1 = botShell.bot().radio(0);
      SWTBotRadio directory1 = botShell.bot().radio(1);
      SWTBotRadio package1 = botShell.bot().radio(2);
      SWTBotText path1 = botShell.bot().text(0);
      SWTBotRadio resource2 = botShell.bot().radio(3);
      SWTBotRadio directory2 = botShell.bot().radio(4);
      SWTBotRadio package2 = botShell.bot().radio(5);
      SWTBotText path2 = botShell.bot().text(1);
      // Test wrong initial values
      if (!initializeWithValidValues) {
         // Test initial values by API
         assertEquals("Package: No existing project or folder defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(control));
         Map<String, Object> values = TestDataSourceUIUtil.getValuesThreadSave(control); 
         assertNotNull(values);
         assertEquals(4, values.size());
         assertEquals(Boolean.TRUE, values.get(UIDummyDriver1.SETTING_BOOLEAN));
         assertEquals(DSPackageManagement.NO_PACKAGES, values.get(UIDummyDriver1.SETTING_PACKAGE_MANAGEMENT));
         assertEquals(new Path(""), values.get(UIDummyDriver1.SETTING_PACKAGE));
         assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_RESOURCE_PACKAGE));
         assertEquals(0, logger.getLog().size());
         // Test initial values by user
         assertTrue(booleanBox.isChecked());
         assertEquals(DSPackageManagement.NO_PACKAGES.getDisplayText(), packageCombo.getText());
         assertTrue(resource1.isSelected());
         assertFalse(directory1.isSelected());
         assertFalse(package1.isSelected());
         assertEquals("", path1.getText());
         assertTrue(resource2.isSelected());
         assertFalse(directory2.isSelected());
         assertFalse(package2.isSelected());
         assertEquals(project.getFullPath().toString(), path2.getText());
         
         // Set valid path to make the rest of the test valid
         path1.setText(project.getFullPath().toString()); // Text throws no modified event
         resource1.click();
         // Test event
         assertEquals(1, logger.getLog().size());
         assertNotNull(logger.getLog().get(0));
         assertEquals(control, logger.getLog().get(0).getSource());
         assertEquals(project.getFullPath(), logger.getLog().get(0).getNewValue());
         assertNull(logger.getLog().get(0).getValidationMessage());
         // Test values by API
         assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(control));
         values = TestDataSourceUIUtil.getValuesThreadSave(control); 
         assertNotNull(values);
         assertEquals(4, values.size());
         assertEquals(Boolean.TRUE, values.get(UIDummyDriver1.SETTING_BOOLEAN));
         assertEquals(DSPackageManagement.NO_PACKAGES, values.get(UIDummyDriver1.SETTING_PACKAGE_MANAGEMENT));
         assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_PACKAGE));
         assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_RESOURCE_PACKAGE));
         // Test values by user
         assertTrue(booleanBox.isChecked());
         assertEquals(DSPackageManagement.NO_PACKAGES.getDisplayText(), packageCombo.getText());
         assertTrue(resource1.isSelected());
         assertFalse(directory1.isSelected());
         assertFalse(package1.isSelected());
         assertEquals(project.getFullPath().toString(), path1.getText());
         assertTrue(resource2.isSelected());
         assertFalse(directory2.isSelected());
         assertFalse(package2.isSelected());
         assertEquals(project.getFullPath().toString(), path2.getText());         
      }
      else {
         // Test initial values by API
         assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(control));
         Map<String, Object> values = TestDataSourceUIUtil.getValuesThreadSave(control); 
         assertNotNull(values);
         assertEquals(4, values.size());
         assertEquals(Boolean.TRUE, values.get(UIDummyDriver1.SETTING_BOOLEAN));
         assertEquals(DSPackageManagement.NO_PACKAGES, values.get(UIDummyDriver1.SETTING_PACKAGE_MANAGEMENT));
         assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_PACKAGE));
         assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_RESOURCE_PACKAGE));
         assertEquals(0, logger.getLog().size());
         // Test initial values by user
         assertTrue(booleanBox.isChecked());
         assertEquals(DSPackageManagement.NO_PACKAGES.getDisplayText(), packageCombo.getText());
         assertTrue(resource1.isSelected());
         assertFalse(directory1.isSelected());
         assertFalse(package1.isSelected());
         assertEquals(project.getFullPath().toString(), path1.getText());
         assertTrue(resource2.isSelected());
         assertFalse(directory2.isSelected());
         assertFalse(package2.isSelected());
         assertEquals(project.getFullPath().toString(), path2.getText());
      }
      // Deselect Boolean by user
      logger.clear();
      booleanBox.deselect();
      // Test event
      assertEquals(1, logger.getLog().size());
      assertNotNull(logger.getLog().get(0));
      assertEquals(control, logger.getLog().get(0).getSource());
      assertEquals(Boolean.FALSE, logger.getLog().get(0).getNewValue());
      assertNull(logger.getLog().get(0).getValidationMessage());
      // Test values by API
      assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(control));
      Map<String, Object>  values = TestDataSourceUIUtil.getValuesThreadSave(control); 
      assertNotNull(values);
      assertEquals(4, values.size());
      assertEquals(Boolean.FALSE, values.get(UIDummyDriver1.SETTING_BOOLEAN));
      assertEquals(DSPackageManagement.NO_PACKAGES, values.get(UIDummyDriver1.SETTING_PACKAGE_MANAGEMENT));
      assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_PACKAGE));
      assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_RESOURCE_PACKAGE));
      // Test values by user
      assertFalse(booleanBox.isChecked());
      assertEquals(DSPackageManagement.NO_PACKAGES.getDisplayText(), packageCombo.getText());
      assertTrue(resource1.isSelected());
      assertFalse(directory1.isSelected());
      assertFalse(package1.isSelected());
      assertEquals(project.getFullPath().toString(), path1.getText());
      assertTrue(resource2.isSelected());
      assertFalse(directory2.isSelected());
      assertFalse(package2.isSelected());
      assertEquals(project.getFullPath().toString(), path2.getText());
      
      // Select new package management by user
      logger.clear();
      packageCombo.setSelection(DSPackageManagement.HIERARCHY.getDisplayText());
      // Test event
      assertEquals(1, logger.getLog().size());
      assertNotNull(logger.getLog().get(0));
      assertEquals(control, logger.getLog().get(0).getSource());
      assertEquals(DSPackageManagement.HIERARCHY, logger.getLog().get(0).getNewValue());
      assertNull(logger.getLog().get(0).getValidationMessage());
      // Test values by API
      assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(control));
      values = TestDataSourceUIUtil.getValuesThreadSave(control); 
      assertNotNull(values);
      assertEquals(4, values.size());
      assertEquals(Boolean.FALSE, values.get(UIDummyDriver1.SETTING_BOOLEAN));
      assertEquals(DSPackageManagement.HIERARCHY, values.get(UIDummyDriver1.SETTING_PACKAGE_MANAGEMENT));
      assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_PACKAGE));
      assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_RESOURCE_PACKAGE));
      // Test values by user
      assertFalse(booleanBox.isChecked());
      assertEquals(DSPackageManagement.HIERARCHY.getDisplayText(), packageCombo.getText());
      assertTrue(resource1.isSelected());
      assertFalse(directory1.isSelected());
      assertFalse(package1.isSelected());
      assertEquals(project.getFullPath().toString(), path1.getText());
      assertTrue(resource2.isSelected());
      assertFalse(directory2.isSelected());
      assertFalse(package2.isSelected());
      assertEquals(project.getFullPath().toString(), path2.getText());
      
      // Select invalid package by user
      logger.clear();
      package1.click();
      // Test event
      assertEquals(1, logger.getLog().size());
      assertNotNull(logger.getLog().get(0));
      assertEquals(control, logger.getLog().get(0).getSource());
      assertNull(logger.getLog().get(0).getNewValue());
      assertEquals("No directory defined.", logger.getLog().get(0).getValidationMessage());
      // Test values by API
      assertEquals("Package: No directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(control));
      values = TestDataSourceUIUtil.getValuesThreadSave(control); 
      assertNotNull(values);
      assertEquals(4, values.size());
      assertEquals(Boolean.FALSE, values.get(UIDummyDriver1.SETTING_BOOLEAN));
      assertEquals(DSPackageManagement.HIERARCHY, values.get(UIDummyDriver1.SETTING_PACKAGE_MANAGEMENT));
      assertNull(values.get(UIDummyDriver1.SETTING_PACKAGE));
      assertEquals(project.getFullPath(), values.get(UIDummyDriver1.SETTING_RESOURCE_PACKAGE));
      // Test values by user
      assertFalse(booleanBox.isChecked());
      assertEquals(DSPackageManagement.HIERARCHY.getDisplayText(), packageCombo.getText());
      assertFalse(resource1.isSelected());
      assertFalse(directory1.isSelected());
      assertTrue(package1.isSelected());
      assertEquals("", path1.getText());
      assertTrue(resource2.isSelected());
      assertFalse(directory2.isSelected());
      assertFalse(package2.isSelected());
      assertEquals(project.getFullPath().toString(), path2.getText());
      
      // Select valid directory by user
      logger.clear();
      directory2.click();
      // Test event
      assertEquals(1, logger.getLog().size());
      assertNotNull(logger.getLog().get(0));
      assertEquals(control, logger.getLog().get(0).getSource());
      assertEquals(ResourceUtil.getLocation(project), logger.getLog().get(0).getNewValue());
      assertNull(logger.getLog().get(0).getValidationMessage());
      // Test values by API
      assertEquals("Package: No directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(control));
      values = TestDataSourceUIUtil.getValuesThreadSave(control); 
      assertNotNull(values);
      assertEquals(4, values.size());
      assertEquals(Boolean.FALSE, values.get(UIDummyDriver1.SETTING_BOOLEAN));
      assertEquals(DSPackageManagement.HIERARCHY, values.get(UIDummyDriver1.SETTING_PACKAGE_MANAGEMENT));
      assertNull(values.get(UIDummyDriver1.SETTING_PACKAGE));
      assertEquals(ResourceUtil.getLocation(project), values.get(UIDummyDriver1.SETTING_RESOURCE_PACKAGE));
      // Test values by user
      assertFalse(booleanBox.isChecked());
      assertEquals(DSPackageManagement.HIERARCHY.getDisplayText(), packageCombo.getText());
      assertFalse(resource1.isSelected());
      assertFalse(directory1.isSelected());
      assertTrue(package1.isSelected());
      assertEquals("", path1.getText());
      assertFalse(resource2.isSelected());
      assertTrue(directory2.isSelected());
      assertFalse(package2.isSelected());
      assertEquals(ResourceUtil.getLocation(project).toString(), path2.getText());
      
      // Remove event logger
      control.removeDataSourceSettingCompositeListener(logger);
      assertEquals(0, control.getDataSourceSettingCompositeListeners().length);
      // Close shell
      control.getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            control.getShell().close();
         }
      });
   }
}