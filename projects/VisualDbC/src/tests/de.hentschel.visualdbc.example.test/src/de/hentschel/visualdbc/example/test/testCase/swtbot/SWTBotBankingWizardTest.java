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

package de.hentschel.visualdbc.example.test.testCase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.PartInitException;
import org.junit.Before;
import org.junit.Test;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.key.model.KeyDriver;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.example.wizard.BankingWizard;
import de.hentschel.visualdbc.generation.ui.test.util.TestGenerationUIUtil;

/**
 * SWT Bot tests for {@link BankingWizard}.
 * @author Martin Hentschel
 */
public class SWTBotBankingWizardTest extends TestCase {
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
      TestGenerationUIUtil.openVisualDbCPerspective();
   }
   
   /**
    * Creates a new test via the example wizard.
    * @throws PartInitException Occurred Exception
    */
   @Test
   public void testExampleProject() throws PartInitException {
      // make sure that the project not exists
      IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject("SWTBotBankingWizardTest");
      assertFalse(project.exists());
      // Open new example wizard
      TestUtilsUtil.menuClick(bot, "File", "New", "Example...");
      SWTBotShell shell = bot.shell("New Example");
      //  Open Banking Example wizard
      TestUtilsUtil.selectInTree(shell.bot().tree(), "Visual DbC", "Banking Example");
      TestUtilsUtil.clickDirectly(shell.bot(), "Next >");
      // Define project name
      SWTBotText text = shell.bot().text(0);
      text.setText(project.getName());
      // Finish wizard
      TestUtilsUtil.clickDirectly(shell.bot(), "Finish");
      shell.bot().waitUntil(Conditions.shellCloses(shell));
      // Make sure that the correct files are added to the new created project
      assertTrue(project.exists());
      IFolder sourceDir = project.getFolder("src");
      assertTrue(sourceDir.exists());
      IFolder bankingDir = sourceDir.getFolder("banking");
      assertTrue(bankingDir.exists());
      IFile bankingDbCFile = bankingDir.getFile("Banking.dbc");
      assertTrue(bankingDbCFile.exists());
      IFile bankingDbCDiagramFile = bankingDir.getFile("Banking.dbc_diagram");
      assertTrue(bankingDbCDiagramFile.exists());
      IFile loggingPayCardFile = bankingDir.getFile("LoggingPayCard.java");
      assertTrue(loggingPayCardFile.exists());
      IFile payCardFile = bankingDir.getFile("PayCard.java");
      assertTrue(payCardFile.exists());
      // Make sure that the correct editor is opened
      SWTBotEditor editor = bot.activeEditor();
      assertNotNull(editor);
      IEditorInput input = editor.getReference().getEditorInput();
      assertNotNull(input);
      IFile file = (IFile)input.getAdapter(IFile.class);
      assertEquals(bankingDbCDiagramFile, file);
      // Close editor
      editor.close();
      // Make sure that diagram model file contains correct connection path
      ResourceSet rst = new ResourceSetImpl();
      Resource resource = rst.getResource(URI.createPlatformResourceURI(bankingDbCFile.getFullPath().toString(), true), true);
      DbcModel model = (DbcModel)resource.getContents().get(0);
      for (DbcProperty property : model.getConnectionSettings()) {
         if (KeyDriver.SETTING_LOCATION.equals(property.getKey())) {
            assertEquals(bankingDir.getFullPath().toString(), property.getValue());
         }
      }
      resource.unload();
   }
}