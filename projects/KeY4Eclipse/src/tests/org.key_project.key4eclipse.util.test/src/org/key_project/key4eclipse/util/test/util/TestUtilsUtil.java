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

import junit.framework.TestCase;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.ui.wizards.JavaCapabilityConfigurationPage;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.key_project.key4eclipse.util.eclipse.Logger;
import org.key_project.key4eclipse.util.java.thread.AbstractRunnableWithResult;
import org.key_project.key4eclipse.util.java.thread.IRunnableWithResult;
import org.key_project.key4eclipse.util.test.Activator;

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
      // Open preference dialog
      TestUtilsUtil.menuClick(bot, "Window", "Preferences");
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
               IEditorPart result = IDE.openEditor(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage(), file);
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
}
