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

package org.key_project.key4eclipse.util.test.util;

import static org.junit.Assert.assertNotNull;

import java.io.ByteArrayInputStream;
import java.util.List;

import javax.swing.tree.TreeModel;

import junit.framework.TestCase;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.ui.wizards.JavaCapabilityConfigurationPage;
import org.eclipse.jface.preference.PreferenceDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.waits.DefaultCondition;
import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.dialogs.PreferencesUtil;
import org.key_project.key4eclipse.util.eclipse.Logger;
import org.key_project.key4eclipse.util.eclipse.WorkbenchUtil;
import org.key_project.key4eclipse.util.java.thread.AbstractRunnableWithResult;
import org.key_project.key4eclipse.util.java.thread.IRunnableWithResult;
import org.key_project.key4eclipse.util.test.Activator;
import org.key_project.swtbot.swing.bot.SwingBot;
import org.key_project.swtbot.swing.bot.SwingBotJButton;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;
import org.key_project.swtbot.swing.bot.SwingBotJTree;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.EnvNode;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.TaskTreeModel;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public class TestUtilsUtil {
   /**
    * Forbid instances.
    */
   private TestUtilsUtil() {
   }
   
   /**
    * Creates a {@link Logger} instance for testing.
    * @return The {@link Logger} instance for testing.
    */
   public static Logger createLogger() {
      return new Logger(Activator.getDefault(), Activator.PLUGIN_ID);
   }
   
   /**
    * Creates a new project and makes sure that it not already exists.
    * @param name The project name.
    * @return The created and opened project.
    * @throws CoreException Occurred Exception.
    */
   public static IProject createProject(String name) {
      try {
         TestCase.assertNotNull(name);
         IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(name);
         if (!project.exists()) {
            project.create(null);
         }
         else {
            TestCase.fail("Project \"" + name + "\" already exists.");
         }
         if (!project.isOpen()) {
            project.open(null);
         }
         return project;
      }
      catch (CoreException e) {
         e.printStackTrace();
         TestCase.fail();
         return null;
      }
   }

   /**
    * Creates a new {@link IJavaProject} that is an {@link IProject} with
    * a JDT nature.
    * @param name The project name.
    * @return The created {@link IJavaProject}.
    * @throws CoreException Occurred Exception.
    * @throws InterruptedException Occurred Exception.
    */
   public static IJavaProject createJavaProject(String name) throws CoreException, InterruptedException {
      IProject project = createProject(name);
      IFolder bin = project.getFolder("bin");
      if (!bin.exists()) {
         bin.create(true, true, null);
      }
      IFolder src = project.getFolder("src");
      if (!src.exists()) {
         src.create(true, true, null);
      }
      IJavaProject javaProject = JavaCore.create(project); 
      JavaCapabilityConfigurationPage page = new JavaCapabilityConfigurationPage();
      page.init(javaProject, bin.getFullPath(), new IClasspathEntry[] {JavaCore.newSourceEntry(src.getFullPath())}, false);
      page.configureJavaProject(null);
      return javaProject;
   }

   /**
    * Creates a new folder and makes sure that it not already exists.
    * @param parent The parent.
    * @param name The folder name.
    * @return The created folder.
    */
   public static IFolder createFolder(IContainer parent, String name) {
      try {
         TestCase.assertNotNull(parent);
         TestCase.assertTrue(parent.exists());
         TestCase.assertNotNull(name);
         IFolder folder = parent.getFolder(new Path(name));
         if (!folder.exists()) {
            folder.create(true, true, null);
         }
         else {
            TestCase.fail("Folder \"" + name + "\" already exists in \"" + parent.getFullPath().toString() + "\".");
         }
         return folder;
      }
      catch (CoreException e) {
         e.printStackTrace();
         TestCase.fail();
         return null;
      }
   }

   /**
    * Creates a new file and makes sure that it not already exists.
    * @param parent The parent container.
    * @param name The name of the file.
    * @param content The content to set in the file.
    * @return The created file.
    */
   public static IFile createFile(IContainer parent, String name, String content) {
      try {
         TestCase.assertNotNull(parent);
         TestCase.assertTrue(parent.exists());
         TestCase.assertNotNull(name);
         TestCase.assertNotNull(content);
         IFile file = parent.getFile(new Path(name));
         if (!file.exists()) {
            file.create(new ByteArrayInputStream(content.getBytes()), true, null);
         }
         else {
            TestCase.fail("File \"" + name + "\" already exists in \"" + parent.getFullPath().toString() + "\".");
         }
         return file;
      }
      catch (CoreException e) {
         e.printStackTrace();
         TestCase.fail();
         return null;
      }
   }

   /**
    * Closes the welcome view if it is opened. Otherwise nothing is done.
    * @param bot The {@link SWTWorkbenchBot} to use.
    */
   public static void closeWelcomeView(SWTWorkbenchBot bot) {
      List<SWTBotView> views = bot.views();
      for (SWTBotView view : views) {
         if ("Welcome".equals(view.getTitle())) {
            view.close();
         }
      }
   }

   /**
    * Selects the project explorer view and the defined path.
    * @param bot The {@link SWTBotTree} to find the package explorer view.
    * @param toSelects The path to select.
    * @return The selected element.
    */
   public static SWTBotTreeItem selectInProjectExplorer(SWTWorkbenchBot bot, String... toSelects) {
      SWTBotView viewBot = null;
      try {
         viewBot = bot.viewByTitle("Package Explorer");
         viewBot.show();
      }
      catch (WidgetNotFoundException e) {
         viewBot = bot.viewByTitle("Project Explorer");
         viewBot.show();
      }
      return selectInTree(viewBot.bot().tree(), toSelects);
   }

   /**
    * Selects the element path in the tree.
    * @param treeBot The {@link SWTBotTree} to select in.
    * @param toSelects The path to select.
    * @return The selected element.
    */
   public static SWTBotTreeItem selectInTree(SWTBotTree treeBot, String... toSelects) {
      SWTBotTreeItem lastItem = null;
      for (String segment : toSelects) {
         if (lastItem == null) {
            lastItem = treeBot.expandNode(segment);
         }
         else {
            lastItem = lastItem.expandNode(segment);
         }
      }
      treeBot.select(lastItem);
      return lastItem;
   }

   /**
    * Executes a click in the main menu.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param menuItems The menu path to click on.
    * @return The menu on that the click was executed.
    */
   public static SWTBotMenu menuClick(SWTWorkbenchBot bot, String... menuItems) {
      SWTBotMenu lastMenu = null;
      for (String menuItem : menuItems) {
         if (lastMenu == null) {
            lastMenu = bot.menu(menuItem);
         }
         else {
            lastMenu = lastMenu.menu(menuItem);
         }
      }
      if (lastMenu != null) {
         lastMenu.click();
         return lastMenu;
      }
      else {
         return null;
      }
   }

   /**
    * Opens the preference page in the preference dialog.
    * @param bot The {@link SWTBot} to use.
    * @param preferencePagePath The path to the preference page to open.
    * @return The opened preference dialog shell.
    */
   public static SWTBotShell openPreferencePage(SWTWorkbenchBot bot, String... preferencePagePath) {
      // Open preference dialog (Usage of TestUtilsUtil.menuClick(bot, "Window", "Preferences") is not possible because Mac OS has entry in special menu)
      Display.getDefault().asyncExec(new Runnable() {
         @Override
         public void run() {
            Shell shell = WorkbenchUtil.getActiveShell();
            PreferenceDialog dialog = PreferencesUtil.createPreferenceDialogOn(shell, null, null, null);
            dialog.open();
         }
      });
      // Open preference page
      SWTBotShell shell = bot.shell("Preferences");
      TestUtilsUtil.selectInTree(shell.bot().tree(), preferencePagePath);
      return shell;
   }
   
   /**
    * Opens an editor for the given file thread save.
    * @param file The file to open.
    * @return The opened {@link IEditorPart}.
    */
   public static IEditorPart openEditor(final IFile file) {
      IRunnableWithResult<IEditorPart> run = new AbstractRunnableWithResult<IEditorPart>() {
         @Override
         public void run() {
            try {
               IEditorPart result = WorkbenchUtil.openEditor(file);
               setResult(result);
            }
            catch (Exception e) {
               setException(e);
            }
         }
      };
      Display.getDefault().syncExec(run);
      if (run.getException() != null) {
         TestCase.fail(run.getException().getMessage());
      }
      IEditorPart result = run.getResult();
      assertNotNull(result);
      return result;
   }

   public static Object getObjectInTree(SWTBotTree treeBot, String... toSelects) {
      final SWTBotTreeItem item = selectInTree(treeBot, toSelects);
      IRunnableWithResult<Object> run = new AbstractRunnableWithResult<Object>() {
         @Override
         public void run() {
            setResult(item.widget.getData());
         }
      };
      Display.getDefault().syncExec(run);
      return run.getResult();
   }
  
   /**
    * Returns the {@link SwingBotJFrame} that handles the {@link MainWindow}
    * of KeY.
    * @return The {@link SwingBotJFrame} for KeY's {@link MainWindow}.
    */
   public static SwingBotJFrame keyGetMainWindow() {
       SwingBot bot = new SwingBot();
       SwingBotJFrame frame = bot.jFrame("KeY " + KeYResourceManager.getManager().getVersion());
       TestCase.assertNotNull(frame);
       TestCase.assertTrue(frame.isOpen());
       return frame;
   }
   
   /**
    * Closes the opened {@link MainWindow} of KeY.
    */
   public static void keyCloseMainWindow() {
       SwingBotJFrame frame = TestUtilsUtil.keyGetMainWindow();
       frame.close();
       TestCase.assertFalse(frame.isOpen());
   }
   
   /**
    * Returns the {@link SwingBotJDialog} that handles the opened
    * {@link ProofManagementDialog} of KeY.
    * @param mainWindow The parent main window.
    * @return The {@link SwingBotJDialog} for the {@link ProofManagementDialog}.
    */
   public static SwingBotJDialog keyGetProofManagementDiaolog(SwingBotJFrame mainWindow) {
       SwingBotJDialog dialog = mainWindow.bot().jDialog("Proof Management");
       TestCase.assertNotNull(dialog);
       TestCase.assertTrue(dialog.isOpen());
       return dialog;
   }
   
   /**
    * Starts the selected proof in the opened {@link ProofManagementDialog}.
    */
   public static void keyStartSelectedProofInProofManagementDiaolog() {
       SwingBotJFrame frame = TestUtilsUtil.keyGetMainWindow();
       SwingBotJDialog dialog = TestUtilsUtil.keyGetProofManagementDiaolog(frame);
       TestCase.assertTrue(dialog.isOpen());
       SwingBotJButton startButton = dialog.bot().jButton("Start Proof");
       startButton.clickAndWait();
       TestCase.assertFalse(dialog.isOpen());
   }
   
   /**
    * Goes to the selected proof in the opened {@link ProofManagementDialog}.
    */
   public static void keyGoToSelectedProofInProofManagementDiaolog() {
       SwingBotJFrame frame = TestUtilsUtil.keyGetMainWindow();
       SwingBotJDialog dialog = TestUtilsUtil.keyGetProofManagementDiaolog(frame);
       TestCase.assertTrue(dialog.isOpen());
       SwingBotJButton goToButton = dialog.bot().jButton("Go to Proof");
       goToButton.clickAndWait();
       TestCase.assertFalse(dialog.isOpen());
   }
   
   /**
    * Makes sure that the correct proofs are shown in the proof tree.
    * @param selectedProof The expected selected proof.
    * @param availableProofs The expected available proofs.
    */
   public static void keyCheckProofs(String selectedProof, String... availableProofs) {
       SwingBotJFrame frame = TestUtilsUtil.keyGetMainWindow();
       SwingBotJTree tree = frame.bot().jTree(TaskTreeModel.class);
       TestUtilsUtil.keyCheckAvailableProofs(tree, availableProofs);
       TestUtilsUtil.keyCheckSelectedProof(tree, selectedProof);
   }
   
   /**
    * Makes sure that the correct proof is selected.
    * @param tree The tree.
    * @param expectedProofName The name of the expected proof.
    */
   public static void keyCheckSelectedProof(SwingBotJTree tree,
                                            String expectedProofName) {
      Object[] selectedObjects = tree.getSelectedObjects();
      TestCase.assertEquals(1, selectedObjects.length);
      TestCase.assertTrue(selectedObjects[0] instanceof TaskTreeNode);
      Proof proof = ((TaskTreeNode)selectedObjects[0]).proof();
      TestCase.assertEquals(expectedProofName, proof.name().toString());
   }

   /**
    * Makes sure that the correct proofs are available.
    * @param tree The tree.
    * @param expectedProofNames The name of the expected proofs.
    */
   public static void keyCheckAvailableProofs(SwingBotJTree tree,
                                              String... expectedProofNames) {
      TreeModel model = tree.getModel();
      TestCase.assertEquals(expectedProofNames.length, model.getChildCount(model.getRoot()));
      for (int i = 0; i < expectedProofNames.length; i++) {
          Object child = model.getChild(model.getRoot(), i);
          TestCase.assertTrue(child instanceof TaskTreeNode);
          Proof proof = ((TaskTreeNode)child).proof();
          TestCase.assertEquals(expectedProofNames[i], proof.name().toString());
      }
   }

   /**
    * Returns the {@link ProofEnvironment} in the proof list at
    * the given index.
    * @param index The index.
    * @return The found {@link ProofEnvironment}.
    */
   public static ProofEnvironment keyGetProofEnv(int index) {
       SwingBotJFrame frame = TestUtilsUtil.keyGetMainWindow();
       SwingBotJTree tree = frame.bot().jTree(TaskTreeModel.class);
       return keyGetProofEnv(tree, index);
   }
   
   /**
    * Returns the {@link ProofEnvironment} in the proof list at
    * the given index.
    * @param tree The {@link SwingBotJTree} to search in.
    * @param index The index.
    * @return The found {@link ProofEnvironment}.
    */
   public static ProofEnvironment keyGetProofEnv(SwingBotJTree tree, int index) {
       TestCase.assertNotNull(tree);
       TestCase.assertTrue(index >= 0);
       TreeModel model = tree.getModel();
       TestCase.assertNotNull(model);
       TestCase.assertTrue(index < model.getChildCount(model.getRoot()));
       Object child = model.getChild(model.getRoot(), index);
       TestCase.assertTrue(child instanceof EnvNode);
       ProofEnvironment result = ((EnvNode)child).getProofEnv();
       return result;
   }
   
   /**
    * Blocks the current {@link Thread} until the given {@link Job} has finished.
    * @param job The {@link Job} to wait for.
    */
   public static void waitForJob(Job job) {
      if (job != null) {
         while (job.getState() != Job.NONE) {
            sleep(100);
         }
         TestCase.assertEquals(Job.NONE, job.getState());
      }
   }
   
   /**
    * Sleeps the current {@link Thread} for the given time.
    * @param time The time to sleep.
    */
   public static void sleep(int time) {
      try {
         Thread.sleep(100);
      }
      catch (InterruptedException e) {
         // Nothing to do.
      }
   }

   /**
    * Returns the specified {@link IMethod}.
    * @param javaProject The {@link IJavaProject} that contains the source code.
    * @param typeName The type name.
    * @param methodName The method name.
    * @param parameters The method parameters.
    * @return The found {@link IMethod}.
    * @throws JavaModelException Occurred Exception.
    */
   public static IMethod getJdtMethod(IJavaProject javaProject,
                                      String typeName, 
                                      String methodName, 
                                      String... parameters) throws JavaModelException {
       IType type = javaProject.findType(typeName);
       assertNotNull(type);
       IMethod method = type.getMethod(methodName, parameters);
       assertNotNull(method);
       return method;
   }

   /**
    * Creates an {@link ICondition} that makes sure that the given 
    * {@link SWTBotTree} has a selection.
    * @param tree The {@link SWTBotTree} to check.
    * @return The created {@link ICondition}.
    */
   public static ICondition hasSelection(final SWTBotTree tree) {
      return new DefaultCondition() {
         @Override
         public boolean test() throws Exception {
            IRunnableWithResult<Boolean> run = new AbstractRunnableWithResult<Boolean>() {
               @Override
               public void run() {
                  setResult(tree.widget.getSelectionCount() >= 1);
               }
            };
            Display.getDefault().syncExec(run);
            return run.getResult() != null && run.getResult().booleanValue();
         }
        
         @Override
         public String getFailureMessage() {
            return "The component " + tree + " has no selection.";
         }
      };
   }
}
