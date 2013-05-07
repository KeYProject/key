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

package org.key_project.util.test.testcase.swtbot;

import java.io.ByteArrayInputStream;
import java.io.IOException;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;
import org.junit.Test;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.wizard.page.ContentWizardNewFileCreationPage;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link ContentWizardNewFileCreationPage}.
 * @author Martin Hentschel
 */
public class SWTBotContentWizardNewFileCreationPageTest extends TestCase {
   /**
    * Tests the creation of a new {@link IFile} in the workspace.
    */
   @Test
   public void testFileCreationInWorkspace() throws IOException, CoreException {
      final IProject project = TestUtilsUtil.createProject("SWTBotContentWizardNewFileCreationPageTest_testFileCreationInWorkspace");
      IFile file = project.getFile("HelloWorld.txt");
      assertFalse(file.exists());
      // Open wizard
      Display.getDefault().asyncExec(new Runnable() {
         @Override
         public void run() {
            TestWizard wizard = new TestWizard();
            wizard.init(PlatformUI.getWorkbench(), SWTUtil.createSelection(project));
            WizardDialog dialog = new WizardDialog(WorkbenchUtil.getActiveShell(), wizard);
            dialog.open();
         }
      });
      // Get wizard
      SWTBot bot = new SWTBot();
      SWTBotShell wizard = bot.shell("Test Wizard");
      TestUtilsUtil.clickDirectly(wizard.bot(), "Finish");
      wizard.bot().waitUntil(Conditions.shellCloses(wizard));
      assertFalse(wizard.isOpen());
      // Make sure that file was created
      assertTrue(file.exists());
      assertEquals("Hello World", IOUtil.readFrom(file.getContents()));
   }
   
   /**
    * {@link Wizard} for test purpose which contains the {@link ContentWizardNewFileCreationPage}.
    * @author Martin Hentschel
    */
   private static class TestWizard extends BasicNewResourceWizard {
      /**
       * The contained {@link ContentWizardNewFileCreationPage}.
       */
      private ContentWizardNewFileCreationPage mainPage;
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void addPages() {
         super.addPages();
         setWindowTitle("Test Wizard");
         mainPage = new ContentWizardNewFileCreationPage("mainPage", getSelection());
         mainPage.setTitle("Test Title");
         mainPage.setDescription("Test Description");
         mainPage.setInitialContents(new ByteArrayInputStream("Hello World".getBytes()));
         mainPage.setFileExtension("txt");
         mainPage.setFileName("HelloWorld.txt");
         addPage(mainPage);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean performFinish() {
         return mainPage.createNewFile() != null;
      }
   }
}