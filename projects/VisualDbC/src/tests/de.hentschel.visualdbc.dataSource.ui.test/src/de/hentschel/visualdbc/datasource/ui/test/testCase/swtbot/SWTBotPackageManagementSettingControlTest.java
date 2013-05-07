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

import junit.framework.TestCase;

import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCombo;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.Test;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.test.util.TestDataSourceUtil;
import de.hentschel.visualdbc.datasource.ui.setting.ISettingControl;
import de.hentschel.visualdbc.datasource.ui.test.util.SettingControlLogger;
import de.hentschel.visualdbc.datasource.ui.test.util.TestDataSourceUIUtil;
import de.hentschel.visualdbc.datasource.ui.util.SettingControlUtil;

/**
 * SWT Bot tests for package management settings controls.
 * @author Martin Hentschel
 */
public class SWTBotPackageManagementSettingControlTest extends TestCase {
   /**
    * Tests getting and setting values by API and user.
    */
   @Test
   public void testGettingAndSettingValues() {
      doTest(new DSPackageManagement[] {DSPackageManagement.HIERARCHY, DSPackageManagement.FLAT_LIST, DSPackageManagement.NO_PACKAGES},
             new DSPackageManagement[] {DSPackageManagement.HIERARCHY, DSPackageManagement.FLAT_LIST, DSPackageManagement.NO_PACKAGES},
             new DSPackageManagement[] {DSPackageManagement.HIERARCHY, DSPackageManagement.FLAT_LIST, DSPackageManagement.NO_PACKAGES});
   }
   
   /**
    * Executes the test.
    * @param valuesToSetByApi Values to set by API.
    * @param valuesToSetByUser Values to set by user.
    * @param valuesToSelectByUser Values to select by user.
    */
   protected void doTest(DSPackageManagement[] valuesToSetByApi,
                         DSPackageManagement[] valuesToSetByUser,
                         DSPackageManagement[] valuesToSelectByUser) {
      // Create control
      final ISettingControl settingControl = SettingControlUtil.createSettingControl("de.hentschel.visualdbc.datasource.ui.setting.PackageManagementControl");
      assertNotNull(settingControl);
      assertEquals(0, settingControl.getSettingControlListeners().length);
      // Add event logger
      SettingControlLogger logger = new SettingControlLogger();
      settingControl.addSettingControlListener(logger);
      assertEquals(1, settingControl.getSettingControlListeners().length);
      assertEquals(logger, settingControl.getSettingControlListeners()[0]);
      // Create shell and UI control instance and set initial value
      IRunnableWithResult<Control> createRun = new AbstractRunnableWithResult<Control>() {
         @Override
         public void run() {
            Shell shell = new Shell(Display.getDefault());
            shell.setText("SWTBotPackageManagementSettingControlTest");
            shell.setLayout(new FillLayout());
            shell.setSize(300, 300);
            Control control = settingControl.createControl(shell);
            setResult(control);
            shell.open();
         }
      };
      Display.getDefault().syncExec(createRun);
      final Control control = createRun.getResult();
      assertNotNull(control);
      // Create bot and get Shell
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotShell botShell = bot.shell("SWTBotPackageManagementSettingControlTest");
      SWTBotCombo botCombo = botShell.bot().comboBox();
      // Test initial value
      assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
      assertEquals(DSPackageManagement.getDefault(), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
      assertEquals(DSPackageManagement.getDefault().getDisplayText(), botCombo.getText());
      assertEquals(0, logger.getLog().size());
      // Set value by API
      for (DSPackageManagement toSet : valuesToSetByApi) {
         logger.clear();
         TestDataSourceUIUtil.setValueThreadSave(settingControl, control, toSet);
         assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
         assertEquals(toSet, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
         assertEquals(toSet.getDisplayText(), botCombo.getText());
         assertEquals(1, logger.getLog().size());
         assertNotNull(logger.getLog().get(0));
         assertEquals(settingControl, logger.getLog().get(0).getSource());
         assertEquals(toSet, logger.getLog().get(0).getNewValue());
         assertNull(logger.getLog().get(0).getValidationMessage());
      }
      // Set value by user
      for (DSPackageManagement toSet : valuesToSetByUser) {
         logger.clear();
         botCombo.setSelection(toSet.getDisplayText());
         assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
         assertEquals(toSet, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
         assertEquals(toSet.getDisplayText(), botCombo.getText());
         assertEquals(1, logger.getLog().size());
         assertNotNull(logger.getLog().get(0));
         assertEquals(settingControl, logger.getLog().get(0).getSource());
         assertEquals(toSet, logger.getLog().get(0).getNewValue());
         assertNull(logger.getLog().get(0).getValidationMessage());
      }
      // Select index by user
      for (DSPackageManagement toSet : valuesToSelectByUser) {
         logger.clear();
         botCombo.setSelection(TestDataSourceUtil.indexOf(toSet));
         assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
         assertEquals(toSet, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
         assertEquals(toSet.getDisplayText(), botCombo.getText());
         assertEquals(1, logger.getLog().size());
         assertNotNull(logger.getLog().get(0));
         assertEquals(settingControl, logger.getLog().get(0).getSource());
         assertEquals(toSet, logger.getLog().get(0).getNewValue());
         assertNull(logger.getLog().get(0).getValidationMessage());
      }
      // Remove event logger
      settingControl.removeSettingControlListener(logger);
      assertEquals(0, settingControl.getSettingControlListeners().length);
      // Close shell
      control.getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            control.getShell().close();
         }
      });
   }
}