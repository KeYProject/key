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

package de.hentschel.visualdbc.generation.ui.test.util;

import static org.junit.Assert.assertEquals;
import junit.framework.TestCase;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Path;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.waits.Conditions;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.generation.ui.wizard.GenerateDiagramWizard;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public final class TestGenerationUIUtil {
   /**
    * Forbid instances.
    */
   private TestGenerationUIUtil() {      
   }

   /**
    * Opens the {@link GenerateDiagramWizard} by selecting it in a new wizard
    * opened via main menu "File -> New -> Other...".
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @return The {@link SWTBotShell} of the opened wizard.
    */
   public static SWTBotShell openGenerateDiagramWizard(SWTWorkbenchBot bot) {
      TestUtilsUtil.menuClick(bot, "File", "New", "Other...");
      SWTBotShell shell = bot.shell("New");
      TestUtilsUtil.selectInTree(shell.bot().tree(), "Visual DbC", "DbC Diagram from Data Source");
      TestUtilsUtil.clickDirectly(shell.bot(), "Next >");
      return shell;
   }

   /**
    * Creates a diagram using the wizard.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param earlyFinishAllowed Early finish allowed?
    * @param diagramContainer The container to store the diagram file in.
    * @param diagramFileName The diagram file name.
    * @param modelContainer The container to store the model file in.
    * @param modelFileName The model file name.
    * @param driver The {@link IDSDriver} to select.
    * @param manipulator Is used, if not {@code null}, to manipulate the driver settings.
    * @param finish Finish or cancel wizard?
    * @param expectedConnection Expected {@link IDSConnection} to compare the created diagram with.
    * @throws DSException Occurred Exception.
    * @throws PartInitException Occurred Exception.
    */
   public static void createDiagramViaGenerateDiagramWizard(SWTWorkbenchBot bot,
                                                            boolean earlyFinishAllowed,
                                                            IContainer diagramContainer,
                                                            String diagramFileName,
                                                            IContainer modelContainer,
                                                            String modelFileName,
                                                            IDSDriver driver,
                                                            ISWTBotShellManipulator manipulator,
                                                            boolean finish,
                                                            IDSConnection expectedConnection) throws DSException, PartInitException {
      // Test parameters
      TestCase.assertNotNull(bot);
      TestCase.assertNotNull(diagramContainer);
      TestCase.assertNotNull(diagramFileName);
      TestCase.assertNotNull(modelContainer);
      TestCase.assertNotNull(modelFileName);
      TestCase.assertNotNull(driver);
      // Make sure that no editor is opened
      assertEquals(0, bot.editors().size());
      // Open wizard
      SWTBotShell shell = openGenerateDiagramWizard(bot);
      assertEquals(earlyFinishAllowed, shell.bot().button("Finish").isEnabled());
      // Handle diagram page
      TestUtilsUtil.selectInTree(shell.bot().tree(), diagramContainer.getFullPath().segments());
      shell.bot().textWithLabel("File name:").setText(diagramFileName);
      TestUtilsUtil.clickDirectly(shell.bot(), "Next >");
      // Handle model page
      TestUtilsUtil.selectInTree(shell.bot().tree(), modelContainer.getFullPath().segments());
      shell.bot().textWithLabel("File name:").setText(modelFileName);
      TestUtilsUtil.clickDirectly(shell.bot(), "Next >");
      // Handle driver page
      shell.bot().comboBoxWithLabel("Data Source").setSelection(driver.getName());
      // Optionally manipulate settings
      if (manipulator != null) {
         manipulator.manipulate(shell);
      }
      // Click finish or cancel
      if (finish) {
         // Finish wizard
         TestUtilsUtil.clickDirectly(shell.bot(), "Finish");
         shell.bot().waitUntil(Conditions.shellCloses(shell));
         // Make sure that correct files are created
         IFile diagramFile = diagramContainer.getFile(new Path(diagramFileName));
         TestCase.assertNotNull(diagramFile);
         TestCase.assertTrue(diagramFile.exists());
         IFile modelFile = modelContainer.getFile(new Path(modelFileName));
         TestCase.assertNotNull(modelFile);
         TestCase.assertTrue(modelFile.exists());
         // Make sure that diagram was opened
         SWTBotEditor editor = bot.activeEditor();
         assertEquals(diagramFileName, editor.getTitle());
         assertEquals(diagramFile, editor.getReference().getEditorInput().getAdapter(IFile.class));
         // Close editor
         editor.close();
         // Make sure that correct diagram was created
         DbcModel dbcModel = TestGenerationUtil.openDbcModel(modelFile);
         TestGenerationUtil.compareModel(expectedConnection, dbcModel);
      }
      else {
         // Cancel wizard
         TestUtilsUtil.clickDirectly(shell.bot(), "Cancel");
         shell.bot().waitUntil(Conditions.shellCloses(shell));
         // Make sure that no file was created
         TestCase.assertFalse(diagramContainer.getFile(new Path(diagramFileName)).exists());
         TestCase.assertFalse(modelContainer.getFile(new Path(modelFileName)).exists());
      }
   }
   
   /**
    * Opens the Visual DbC perspective.
    */
   public static void openVisualDbCPerspective() {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().setPerspective(getVisualDbCPerspective());
         }
      });
   }
   
   /**
    * Returns the Visual DbC perspective. 
    * @return The Visual DbC perspective.
    */
   public static IPerspectiveDescriptor getVisualDbCPerspective() {
      return getPerspective("de.hentschel.visualdbc.perspective");
   }
   
   /**
    * Returns the perspective with the given ID.
    * @param id The ID to search.
    * @return The foudn perspective or {@code null} if no perspective was found.
    */
   public static IPerspectiveDescriptor getPerspective(String id) {
      IPerspectiveDescriptor result = null;
      IPerspectiveDescriptor[] perspectives = PlatformUI.getWorkbench().getPerspectiveRegistry().getPerspectives();
      int i = 0;
      while (result == null && i < perspectives.length) {
         if (ObjectUtil.equals(perspectives[i].getId(), id)) {
            result = perspectives[i];
         }
         i++;
      }
      return result;
   }
}