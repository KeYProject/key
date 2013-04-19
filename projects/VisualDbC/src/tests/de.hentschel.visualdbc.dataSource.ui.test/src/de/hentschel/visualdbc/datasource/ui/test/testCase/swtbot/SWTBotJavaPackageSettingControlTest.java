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

import java.io.File;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.utils.TableCollection;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotRadio;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.Test;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.ui.setting.ISettingControl;
import de.hentschel.visualdbc.datasource.ui.test.Activator;
import de.hentschel.visualdbc.datasource.ui.test.util.SettingControlLogger;
import de.hentschel.visualdbc.datasource.ui.test.util.TestDataSourceUIUtil;
import de.hentschel.visualdbc.datasource.ui.util.SettingControlUtil;

/**
 * SWT Bot tests for java package settings controls.
 * @author Martin Hentschel
 */
public class SWTBotJavaPackageSettingControlTest extends TestCase {
   /**
    * Tests error messages on the file tab.
    */
   @Test
   public void testPackageErrorMessages() throws CoreException, InterruptedException {
       // Create project
       IJavaProject javaProject = createProject();
       IProject project = javaProject.getProject();
       assertTrue(project.exists());
       IFolder srcFolder = project.getFolder("src");
       assertTrue(srcFolder.exists());
       IFolder packageAFolder = srcFolder.getFolder("sWTBotJavaPackageSettingControlTestA");
       assertTrue(packageAFolder.exists());
       IPackageFragmentRoot[] roots = javaProject.getPackageFragmentRoots();
       assertTrue(roots.length >= 1);
       IPackageFragmentRoot defaultPackage = roots[0];
       assertNotNull(defaultPackage);
       IPackageFragment packageA = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestA");
       assertNotNull(packageA);
       IPackageFragment packageB = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestB");
       assertNotNull(packageB);
       // Create control
       final ISettingControl settingControl = SettingControlUtil.createSettingControl(getControlId());
       assertNotNull(settingControl);
       assertEquals(0, settingControl.getSettingControlListeners().length);
       // Create shell and UI control instance and set initial value
       IRunnableWithResult<Control> createRun = new AbstractRunnableWithResult<Control>() {
          @Override
          public void run() {
             Shell shell = new Shell(Display.getDefault());
             shell.setText("SWTBotJavaPackageSettingControlTest");
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
       try {
           // Create bot and get Shell
           SWTWorkbenchBot bot = new SWTWorkbenchBot();
           SWTBotShell botShell = bot.shell("SWTBotJavaPackageSettingControlTest");
           SWTBotRadio resourceRadio = botShell.bot().radio("Resource");
           SWTBotRadio packageRadio = botShell.bot().radio("Package");
           SWTBotText pathText = botShell.bot().text();
           // Select type
           packageRadio.click();
           // Test initial value
           assertEquals("No directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertNull(TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch to other invalid type
           resourceRadio.click();
           assertEquals("No existing project or folder defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new Path(""), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch back from invalid type
           packageRadio.click();
           assertEquals("No directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertNull(TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch to other invalid type and make it valid
           resourceRadio.click();
           assertEquals("No existing project or folder defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new Path(""), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           pathText.setText(packageB.getPath().toString());
           assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(packageB.getPath(), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch back from valid type
           packageRadio.click();
           assertEquals("No directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertNull(TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
       }
       finally {
           // Close shell
           if (control != null) {
               control.getDisplay().syncExec(new Runnable() {
                   @Override
                   public void run() {
                      control.getShell().close();
                   }
                });
           }
       }
   }
   
   /**
    * Tests error messages on the file tab.
    */
   @Test
   public void testFileErrorMessages() throws CoreException, InterruptedException {
       // Create project
       IJavaProject javaProject = createProject();
       IProject project = javaProject.getProject();
       assertTrue(project.exists());
       IFolder srcFolder = project.getFolder("src");
       assertTrue(srcFolder.exists());
       IFolder packageAFolder = srcFolder.getFolder("sWTBotJavaPackageSettingControlTestA");
       assertTrue(packageAFolder.exists());
       IPackageFragmentRoot[] roots = javaProject.getPackageFragmentRoots();
       assertTrue(roots.length >= 1);
       IPackageFragmentRoot defaultPackage = roots[0];
       assertNotNull(defaultPackage);
       IPackageFragment packageA = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestA");
       assertNotNull(packageA);
       IPackageFragment packageB = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestB");
       assertNotNull(packageB);
       // Create control
       final ISettingControl settingControl = SettingControlUtil.createSettingControl(getControlId());
       assertNotNull(settingControl);
       assertEquals(0, settingControl.getSettingControlListeners().length);
       // Create shell and UI control instance and set initial value
       IRunnableWithResult<Control> createRun = new AbstractRunnableWithResult<Control>() {
          @Override
          public void run() {
             Shell shell = new Shell(Display.getDefault());
             shell.setText("SWTBotJavaPackageSettingControlTest");
             shell.setLayout(new FillLayout());
             shell.setSize(300, 300);
             Control control = settingControl.createControl(shell);
             setResult(control);
             shell.open();
          }
       };
       Display.getDefault().syncExec(createRun);
       final Control control = createRun.getResult();
       try {
           assertNotNull(control);
           // Create bot and get Shell
           SWTWorkbenchBot bot = new SWTWorkbenchBot();
           SWTBotShell botShell = bot.shell("SWTBotJavaPackageSettingControlTest");
           SWTBotRadio fileRadio = botShell.bot().radio("Directory");
           SWTBotRadio packageRadio = botShell.bot().radio("Package");
           SWTBotText pathText = botShell.bot().text();
           // Select type
           fileRadio.click();
           // Test initial value
           assertEquals("No existing directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new File(""), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Set invalid path
           pathText.setText("INVALID");
           assertEquals("No existing directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new File("INVALID"), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Set valid path
           pathText.setText(ResourceUtil.getLocation(packageA.getResource()).toString());
           assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(ResourceUtil.getLocation(packageA.getResource()), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Set invalid path
           pathText.setText("INVALID");
           assertEquals("No existing directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new File("INVALID"), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch to other invalid type
           packageRadio.click();
           assertEquals("No directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertNull(TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch back from invalid type
           fileRadio.click();
           assertEquals("No existing directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new File("INVALID"), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch to other invalid type and make it valid
           packageRadio.click();
           assertEquals("No directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertNull(TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           botShell.bot().button().click();
           SWTBotShell selectShell = botShell.bot().shell("Select package");
           selectShell.bot().text().setText(packageB.getElementName()); // Filter the table entries, required in tests if scroll bars are used.
           selectShell.bot().table().select(packageB.getElementName());
           selectShell.bot().button("OK").click();
           assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(getExpectedPackage(packageB), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch back from valid type
           fileRadio.click();
           assertEquals("No existing directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new File("INVALID"), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
        }
        finally {
            // Close shell
            if (control != null) {
                control.getDisplay().syncExec(new Runnable() {
                    @Override
                    public void run() {
                       control.getShell().close();
                    }
                 });
            }
        }
   }
   
   /**
    * Returns the expected value for the given {@link IJavaElement}.
    * @param element The given {@link IJavaElement}.
    * @return The expected value.
    */
   protected Object getExpectedPackage(IJavaElement element) {
      return element;
   }
   
   /**
    * Tests error messages on the resource tab.
    */
   @Test
   public void testResourceErrorMessages() throws CoreException, InterruptedException {
       // Create project
       IJavaProject javaProject = createProject();
       IProject project = javaProject.getProject();
       assertTrue(project.exists());
       IFolder srcFolder = project.getFolder("src");
       assertTrue(srcFolder.exists());
       IFolder packageAFolder = srcFolder.getFolder("sWTBotJavaPackageSettingControlTestA");
       assertTrue(packageAFolder.exists());
       IPackageFragmentRoot[] roots = javaProject.getPackageFragmentRoots();
       assertTrue(roots.length >= 1);
       IPackageFragmentRoot defaultPackage = roots[0];
       assertNotNull(defaultPackage);
       IPackageFragment packageA = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestA");
       assertNotNull(packageA);
       IPackageFragment packageB = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestB");
       assertNotNull(packageB);
       // Create control
       final ISettingControl settingControl = SettingControlUtil.createSettingControl(getControlId());
       assertNotNull(settingControl);
       assertEquals(0, settingControl.getSettingControlListeners().length);
       // Create shell and UI control instance and set initial value
       IRunnableWithResult<Control> createRun = new AbstractRunnableWithResult<Control>() {
          @Override
          public void run() {
             Shell shell = new Shell(Display.getDefault());
             shell.setText("SWTBotJavaPackageSettingControlTest");
             shell.setLayout(new FillLayout());
             shell.setSize(300, 300);
             Control control = settingControl.createControl(shell);
             setResult(control);
             shell.open();
          }
       };
       Display.getDefault().syncExec(createRun);
       final Control control = createRun.getResult();
       try {
           assertNotNull(control);
           // Create bot and get Shell
           SWTWorkbenchBot bot = new SWTWorkbenchBot();
           SWTBotShell botShell = bot.shell("SWTBotJavaPackageSettingControlTest");
           SWTBotRadio resourceRadio = botShell.bot().radio("Resource");
           SWTBotRadio fileRadio = botShell.bot().radio("Directory");
           SWTBotText pathText = botShell.bot().text();
           // Select type
           resourceRadio.click();
           // Test initial value
           assertEquals("No existing project or folder defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new Path(""), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Set invalid path
           pathText.setText("INVALID");
           assertEquals("No existing project or folder defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new Path("INVALID"), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Set valid path
           pathText.setText(packageA.getPath().toString());
           assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(packageA.getPath(), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Set invalid path
           pathText.setText("INVALID");
           assertEquals("No existing project or folder defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new Path("INVALID"), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch to other invalid type
           fileRadio.click();
           assertEquals("No existing directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new File(""), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch back from invalid type
           resourceRadio.click();
           assertEquals("No existing project or folder defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new Path("INVALID"), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch to other invalid type and make it valid
           fileRadio.click();
           assertEquals("No existing directory defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new File(""), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           pathText.setText(ResourceUtil.getLocation(packageB.getResource()).toString());
           assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(ResourceUtil.getLocation(packageB.getResource()), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           // Switch back from valid type
           resourceRadio.click();
           assertEquals("No existing project or folder defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
           assertEquals(new Path("INVALID"), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
        }
        finally {
            // Close shell
            if (control != null) {
                control.getDisplay().syncExec(new Runnable() {
                   @Override
                   public void run() {
                      control.getShell().close();
                   }
                });
            }
        }
   }
   
   /**
    * Tests the select button for packages.
    */
   @Test
   public void testSelectingPackage() throws CoreException, InterruptedException {
       // Create project
       IJavaProject javaProject = createProject();
       IProject project = javaProject.getProject();
       assertTrue(project.exists());
       IFolder srcFolder = project.getFolder("src");
       assertTrue(srcFolder.exists());
       IFolder packageAFolder = srcFolder.getFolder("sWTBotJavaPackageSettingControlTestA");
       assertTrue(packageAFolder.exists());
       IPackageFragmentRoot[] roots = javaProject.getPackageFragmentRoots();
       assertTrue(roots.length >= 1);
       IPackageFragmentRoot defaultPackage = roots[0];
       assertNotNull(defaultPackage);
       IPackageFragment packageA = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestA");
       assertNotNull(packageA);
       IPackageFragment packageB = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestB");
       assertNotNull(packageB);
       // Create control
       final ISettingControl settingControl = SettingControlUtil.createSettingControl(getControlId());
       assertNotNull(settingControl);
       assertEquals(0, settingControl.getSettingControlListeners().length);
       // Create shell and UI control instance and set initial value
       IRunnableWithResult<Control> createRun = new AbstractRunnableWithResult<Control>() {
          @Override
          public void run() {
             Shell shell = new Shell(Display.getDefault());
             shell.setText("SWTBotJavaPackageSettingControlTest");
             shell.setLayout(new FillLayout());
             shell.setSize(300, 300);
             Control control = settingControl.createControl(shell);
             setResult(control);
             shell.open();
          }
       };
       Display.getDefault().syncExec(createRun);
       final Control control = createRun.getResult();
       try {
           assertNotNull(control);
           // Create bot and get Shell
           SWTWorkbenchBot bot = new SWTWorkbenchBot();
           SWTBotShell botShell = bot.shell("SWTBotJavaPackageSettingControlTest");
           SWTBotRadio packageRadio = botShell.bot().radio("Package");
           SWTBotText pathText = botShell.bot().text();
           SWTBotButton clickButton = botShell.bot().button();
           // Select type
           packageRadio.click();
           // Select package a
           clickButton.click();
           SWTBotShell selectShell = botShell.bot().shell("Select package");
           selectShell.bot().text().setText(packageA.getElementName()); // Filter the table entries, required in tests if scroll bars are used.
           selectShell.bot().table().select(packageA.getElementName());
           selectShell.bot().button("OK").click();
           assertEquals(getExpectedPackage(packageA), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           assertEquals(packageA.getElementName(), pathText.getText());
           // Select package b, package a must be preselected (not testable)
           clickButton.click();
           selectShell = botShell.bot().shell("Select package");
           selectShell.bot().text().setText(packageB.getElementName()); // Filter the table entries, required in tests if scroll bars are used.
           selectShell.bot().table().select(packageB.getElementName());
           selectShell.bot().button("OK").click();
           assertEquals(getExpectedPackage(packageB), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           assertEquals(packageB.getElementName(), pathText.getText());
        }
        finally {
            // Close shell
            if (control != null) {
                control.getDisplay().syncExec(new Runnable() {
                    @Override
                    public void run() {
                       control.getShell().close();
                    }
                 });
            }
        }
   }
   
   /**
    * Tests the select button for resources.
    */
   @Test
   public void testSelectingResource() throws CoreException, InterruptedException {
       // Create project
       IJavaProject javaProject = createProject();
       IProject project = javaProject.getProject();
       assertTrue(project.exists());
       IFolder srcFolder = project.getFolder("src");
       assertTrue(srcFolder.exists());
       IFolder packageAFolder = srcFolder.getFolder("sWTBotJavaPackageSettingControlTestA");
       assertTrue(packageAFolder.exists());
       IPackageFragmentRoot[] roots = javaProject.getPackageFragmentRoots();
       assertTrue(roots.length >= 1);
       IPackageFragmentRoot defaultPackage = roots[0];
       assertNotNull(defaultPackage);
       IPackageFragment packageA = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestA");
       assertNotNull(packageA);
       IPackageFragment packageB = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestB");
       assertNotNull(packageB);
       // Create control
       final ISettingControl settingControl = SettingControlUtil.createSettingControl(getControlId());
       assertNotNull(settingControl);
       assertEquals(0, settingControl.getSettingControlListeners().length);
       // Create shell and UI control instance and set initial value
       IRunnableWithResult<Control> createRun = new AbstractRunnableWithResult<Control>() {
          @Override
          public void run() {
             Shell shell = new Shell(Display.getDefault());
             shell.setText("SWTBotJavaPackageSettingControlTest");
             shell.setLayout(new FillLayout());
             shell.setSize(300, 300);
             Control control = settingControl.createControl(shell);
             setResult(control);
             shell.open();
          }
       };
       Display.getDefault().syncExec(createRun);
       final Control control = createRun.getResult();
       try {
           assertNotNull(control);
           // Create bot and get Shell
           SWTWorkbenchBot bot = new SWTWorkbenchBot();
           SWTBotShell botShell = bot.shell("SWTBotJavaPackageSettingControlTest");
           SWTBotRadio resourceRadio = botShell.bot().radio("Resource");
           SWTBotText pathText = botShell.bot().text();
           SWTBotButton clickButton = botShell.bot().button();
           // Select type
           resourceRadio.click();
           // Select package a
           clickButton.click();
           SWTBotShell selectShell = botShell.bot().shell("Select container");
           String[] segments = packageA.getResource().getFullPath().segments();
           TestUtilsUtil.selectInTree(selectShell.bot().tree(), segments);
           selectShell.bot().button("OK").click();
           assertEquals(packageA.getResource().getFullPath(), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           assertEquals(packageA.getPath().toString(), pathText.getText());
           // Select package b, package a must be preselected
           clickButton.click();
           selectShell = botShell.bot().shell("Select container");
           TableCollection selection = selectShell.bot().tree().selection();
           assertEquals(1, selection.rowCount());
           assertEquals(packageA.getElementName(), selection.get(0).get(0));
           segments = packageB.getResource().getFullPath().segments();
           TestUtilsUtil.selectInTree(selectShell.bot().tree(), segments);
           selectShell.bot().button("OK").click();
           assertEquals(packageB.getResource().getFullPath(), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
           assertEquals(packageB.getPath().toString(), pathText.getText());
       }
       finally {
           // Close shell
           if (control != null) {
               control.getDisplay().syncExec(new Runnable() {
                   @Override
                   public void run() {
                      control.getShell().close();
                   }
                });
           }
       }
   }
   
   /**
    * Tests getting and setting values by API and user.
    */
   @Test
   public void testGettingAndSettingValues() throws Exception {
       IJavaProject javaProject = createProject();
       IProject project = javaProject.getProject();
       assertTrue(project.exists());
       IFolder srcFolder = project.getFolder("src");
       assertTrue(srcFolder.exists());
       IFolder packageAFolder = srcFolder.getFolder("sWTBotJavaPackageSettingControlTestA");
       assertTrue(packageAFolder.exists());
       IPackageFragmentRoot[] roots = javaProject.getPackageFragmentRoots();
       assertTrue(roots.length >= 1);
       IPackageFragmentRoot defaultPackage = roots[0];
       assertNotNull(defaultPackage);
       IPackageFragment packageA = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestA");
       assertNotNull(packageA);
       IPackageFragment packageB = defaultPackage.getPackageFragment("sWTBotJavaPackageSettingControlTestB");
       assertNotNull(packageB);
       doTest(new Object[] {packageA, project, ResourceUtil.getLocation(packageAFolder), javaProject, defaultPackage},
              new Object[] {project, packageAFolder, ResourceUtil.getLocation(project), ResourceUtil.getLocation(packageAFolder), packageA, packageB});
   }
   
   /**
    * Creates the project with the test data.
    * @return The created project.
    * @throws CoreException Occurred Exception
    * @throws InterruptedException Occurred Exception
    */
   protected IJavaProject createProject() throws CoreException, InterruptedException {
      // Create if exists
      IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject("SWTBotJavaPackageSettingControlTest");
      if (!project.exists()) {
          // Create project
          IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotJavaPackageSettingControlTest");
          project = javaProject.getProject();
          assertTrue(project.exists());
          IFolder srcFolder = project.getFolder("src");
          assertTrue(srcFolder.exists());
          BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/javaPackageSettingControlTest", srcFolder);
          TestUtilsUtil.waitForBuild();
          TestUtilsUtil.waitForJobs();
          return javaProject;
      }
      else {
          return JDTUtil.getJavaProject(project);
      }
   }
   
   /**
    * Executes the test.
    * @param valuesToSetByApi Values to set by API.
    * @param valuesToSetByUser Values to set by user.
    * @throws Exception Occurred Exception. 
    */
   protected void doTest(Object[] valuesToSetByApi,
                         Object[] valuesToSetByUser) throws Exception {
      // Create control
      final ISettingControl settingControl = SettingControlUtil.createSettingControl(getControlId());
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
            try {
                Shell shell = new Shell(Display.getDefault());
                shell.setText("SWTBotJavaPackageSettingControlTest");
                shell.setLayout(new FillLayout());
                shell.setSize(300, 300);
                Control control = settingControl.createControl(shell);
                setResult(control);
                shell.open();
            }
            catch (Exception e) {
                setException(e);
            }
         }
      };
      Display.getDefault().syncExec(createRun);
      if (createRun.getException() != null) {
          throw createRun.getException();
      }
      final Control control = createRun.getResult();
      try {
        assertNotNull(control);
          // Create bot and get Shell
          SWTWorkbenchBot bot = new SWTWorkbenchBot();
          SWTBotShell botShell = bot.shell("SWTBotJavaPackageSettingControlTest");
          SWTBotRadio resourceRadio = botShell.bot().radio("Resource");
          SWTBotRadio fileRadio = botShell.bot().radio("Directory");
          SWTBotRadio packageRadio = botShell.bot().radio("Package");
          SWTBotText pathText = botShell.bot().text();
          SWTBotButton clickButton = botShell.bot().button();
          // Test initial value
          assertEquals("No existing project or folder defined.", TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
          assertEquals(new Path(""), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
          assertEquals(true, resourceRadio.isSelected());
          assertEquals(false, fileRadio.isSelected());
          assertEquals(false, packageRadio.isSelected());
          assertEquals("", pathText.getText());
          IPath oldResource = null;
          File oldFile = null;
          IJavaElement oldJavaElement = null;
          // Set value by API
          for (Object toSet : valuesToSetByApi) {
             logger.clear();
             TestDataSourceUIUtil.setValueThreadSave(settingControl, control, toSet);
             assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
             assertEquals(1, logger.getLog().size());
             assertNotNull(logger.getLog().get(0));
             assertEquals(settingControl, logger.getLog().get(0).getSource());
             assertNull(logger.getLog().get(0).getValidationMessage());
             if (toSet instanceof File) {
                // Update old values
                oldFile = (File)toSet;
                // Test event and current value
                assertEquals(toSet, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                assertEquals(false, resourceRadio.isSelected());
                assertEquals(true, fileRadio.isSelected());
                assertEquals(false, packageRadio.isSelected());
                assertEquals(toSet.toString(), pathText.getText());
                assertEquals(toSet, logger.getLog().get(0).getNewValue());
                // Test modification of other value kinds
                resourceRadio.click();
                assertEquals(oldResource, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                packageRadio.click();
                assertEquals(getExpectedPackage(oldJavaElement), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                fileRadio.click();
                assertEquals(oldFile, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
             }
             else if (toSet instanceof IResource) {
                // Update old values
                oldResource = ((IResource)toSet).getFullPath();
                oldFile = ResourceUtil.getLocation((IResource)toSet);
                // Test event and current value
                assertEquals(((IResource)toSet).getFullPath(), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                assertEquals(true, resourceRadio.isSelected());
                assertEquals(false, fileRadio.isSelected());
                assertEquals(false, packageRadio.isSelected());
                assertEquals(((IResource)toSet).getFullPath().toString(), pathText.getText());
                assertEquals(((IResource)toSet).getFullPath(), logger.getLog().get(0).getNewValue());
                // Test modification of other value kinds
                packageRadio.click();
                assertEquals(getExpectedPackage(oldJavaElement), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                fileRadio.click();
                assertEquals(oldFile, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                resourceRadio.click();
                assertEquals(oldResource, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
             }
             else if (toSet instanceof IJavaElement) {
                IJavaElement packageElement = JDTUtil.getPackage((IJavaElement)toSet);
                if (packageElement != null) {
                   // Update old values
                   oldJavaElement = (IJavaElement)toSet;
                   oldResource = ((IJavaElement)toSet).getPath();
                   oldFile = ResourceUtil.getLocation(((IJavaElement)toSet).getResource());
                   // Test event and current value
                   assertEquals(getExpectedPackage((IJavaElement)toSet), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                   assertEquals(false, resourceRadio.isSelected());
                   assertEquals(false, fileRadio.isSelected());
                   assertEquals(true, packageRadio.isSelected());
                   assertEquals(((IJavaElement)toSet).getElementName(), pathText.getText());
                   assertEquals(getExpectedPackage((IJavaElement)toSet), logger.getLog().get(0).getNewValue());
                   // Test modification of other value kinds
                   resourceRadio.click();
                   assertEquals(oldResource, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                   fileRadio.click();
                   assertEquals(oldFile, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                   packageRadio.click();
                   assertEquals(getExpectedPackage(oldJavaElement), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                }
                else {
                   // Update old values
                   toSet = ((IJavaElement)toSet).getResource();
                   oldResource = ((IResource)toSet).getFullPath();
                   oldFile = ResourceUtil.getLocation((IResource)toSet);
                   // Test event and current value
                   assertEquals(((IResource)toSet).getFullPath(), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                   assertEquals(true, resourceRadio.isSelected());
                   assertEquals(false, fileRadio.isSelected());
                   assertEquals(false, packageRadio.isSelected());
                   assertEquals(((IResource)toSet).getFullPath().toString(), pathText.getText());
                   assertEquals(((IResource)toSet).getFullPath(), logger.getLog().get(0).getNewValue());
                   // Test modification of other value kinds
                   packageRadio.click();
                   assertEquals(getExpectedPackage(oldJavaElement), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                   fileRadio.click();
                   assertEquals(oldFile, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                   resourceRadio.click();
                   assertEquals(oldResource, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                }
             }
             else {
                fail("Unsupported value kind");
             }
          }
          // Set value by user
          for (Object toSet : valuesToSetByUser) {
             logger.clear();
             if (toSet instanceof File) {
                if (!fileRadio.isSelected()) {
                   fileRadio.click();
                   assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
                   assertEquals(1, logger.getLog().size());
                   assertNotNull(logger.getLog().get(0));
                   assertEquals(settingControl, logger.getLog().get(0).getSource());
                   assertNull(logger.getLog().get(0).getValidationMessage());
                   assertEquals(oldFile, logger.getLog().get(0).getNewValue());
                   logger.clear();
                }
                pathText.setText(toSet.toString());
             }
             else if (toSet instanceof IResource) {
                if (!resourceRadio.isSelected()) {
                   resourceRadio.click();
                   assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
                   assertEquals(1, logger.getLog().size());
                   assertNotNull(logger.getLog().get(0));
                   assertEquals(settingControl, logger.getLog().get(0).getSource());
                   assertNull(logger.getLog().get(0).getValidationMessage());
                   assertEquals(oldResource, logger.getLog().get(0).getNewValue());
                   logger.clear();
                }
                pathText.setText(((IResource)toSet).getFullPath().toString());
             }
             else if (toSet instanceof IJavaElement) {
                if (!packageRadio.isSelected()) {
                   packageRadio.click();
                   assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
                   assertEquals(1, logger.getLog().size());
                   assertNotNull(logger.getLog().get(0));
                   assertEquals(settingControl, logger.getLog().get(0).getSource());
                   assertNull(logger.getLog().get(0).getValidationMessage());
                   assertEquals(getExpectedPackage(oldJavaElement), logger.getLog().get(0).getNewValue());
                   logger.clear();
                }
                clickButton.click();
                SWTBotShell selectShell = botShell.bot().shell("Select package");
                selectShell.bot().text().setText(((IJavaElement)toSet).getElementName()); // Filter the table entries, required in tests if scroll bars are used.
                selectShell.bot().table().select(((IJavaElement)toSet).getElementName());
                selectShell.bot().button("OK").click();
             }
             else {
                fail("Unsupported value kind");
             }
             assertNull(TestDataSourceUIUtil.getValidationMessageThreadSave(settingControl, control));
             assertEquals(1, logger.getLog().size());
             assertNotNull(logger.getLog().get(0));
             assertEquals(settingControl, logger.getLog().get(0).getSource());
             assertNull(logger.getLog().get(0).getValidationMessage());
             if (toSet instanceof File) {
                // Update old values
                oldFile = (File)toSet;
                // Test event and current value
                assertEquals(toSet, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                assertEquals(false, resourceRadio.isSelected());
                assertEquals(true, fileRadio.isSelected());
                assertEquals(false, packageRadio.isSelected());
                assertEquals(toSet.toString(), pathText.getText());
                assertEquals(toSet, logger.getLog().get(0).getNewValue());
                // Test modification of other value kinds
                resourceRadio.click();
                assertEquals(oldResource, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                packageRadio.click();
                assertEquals(getExpectedPackage(oldJavaElement), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                fileRadio.click();
                assertEquals(oldFile, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
             }
             else if (toSet instanceof IResource) {
                // Update old values
                oldResource = ((IResource)toSet).getFullPath();
                // Test event and current value
                assertEquals(((IResource)toSet).getFullPath(), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                assertEquals(true, resourceRadio.isSelected());
                assertEquals(false, fileRadio.isSelected());
                assertEquals(false, packageRadio.isSelected());
                assertEquals(((IResource)toSet).getFullPath().toString(), pathText.getText());
                assertEquals(((IResource)toSet).getFullPath(), logger.getLog().get(0).getNewValue());
                // Test modification of other value kinds
                packageRadio.click();
                assertEquals(getExpectedPackage(oldJavaElement), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                fileRadio.click();
                assertEquals(toSet.toString(), oldFile, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                resourceRadio.click();
                assertEquals(oldResource, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
             }
             else if (toSet instanceof IJavaElement) {
                // Update old values
                oldJavaElement = (IJavaElement)toSet;
                // Test event and current value
                assertEquals(getExpectedPackage((IJavaElement)toSet), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                assertEquals(false, resourceRadio.isSelected());
                assertEquals(false, fileRadio.isSelected());
                assertEquals(true, packageRadio.isSelected());
                assertEquals(((IJavaElement)toSet).getElementName(), pathText.getText());
                assertEquals(getExpectedPackage((IJavaElement)toSet), logger.getLog().get(0).getNewValue());
                // Test modification of other value kinds
                resourceRadio.click();
                assertEquals(oldResource, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                fileRadio.click();
                assertEquals(oldFile, TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
                packageRadio.click();
                assertEquals(getExpectedPackage(oldJavaElement), TestDataSourceUIUtil.getValueThreadSave(settingControl, control));
             }
             else {
                fail("Unsupported value kind");
             }
          }
          // Remove event logger
          settingControl.removeSettingControlListener(logger);
          assertEquals(0, settingControl.getSettingControlListeners().length);
      }
      finally {
         // Close shell
         if (control != null) {
            control.getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  control.getShell().close();
               }
            });
         }
      }
   }

   /**
    * The id of the control to use.
    * @return The control id.
    */
   protected String getControlId() {
      return "de.hentschel.visualdbc.datasource.ui.setting.JavaPackageSettingControl";
   }
}