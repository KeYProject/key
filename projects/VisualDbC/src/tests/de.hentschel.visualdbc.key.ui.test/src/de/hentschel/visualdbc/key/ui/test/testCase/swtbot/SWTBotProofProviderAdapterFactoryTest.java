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

package de.hentschel.visualdbc.key.ui.test.testCase.swtbot;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.emf.common.util.URI;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.SWTGefBot;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditPart;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IEditorPart;
import org.junit.Test;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.util.KeYExampleUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.key.model.KeyDriver;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.dbcmodel.presentation.DbcmodelEditor;
import de.hentschel.visualdbc.interactive.proving.ui.job.StartProofJob;
import de.hentschel.visualdbc.interactive.proving.ui.test.util.TestInteractiveProvingUtil;
import de.hentschel.visualdbc.interactive.proving.ui.test.util.TestInteractiveProvingUtil.LogStartProofJobListener;
import de.hentschel.visualdbc.interactive.proving.ui.util.DbcModelUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveConnectionUtil;
import de.hentschel.visualdbc.key.ui.adapter.ProofProviderAdapterFactory;
import de.hentschel.visualdbc.key.ui.test.Activator;
import de.hentschel.visualdbc.key.ui.test.testCase.AbstractProofReferenceModelCreatorTest;
import de.hentschel.visualdbc.key.ui.view.ProofDependenciesViewPart;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * SWTBot tests for {@link ProofProviderAdapterFactory} which is used to
 * show dbc diagrams in the {@link ProofDependenciesViewPart}.
 * @author Martin Hentschel
 */
public class SWTBotProofProviderAdapterFactoryTest extends AbstractProofReferenceModelCreatorTest {
   /**
    * Tests the returned adapter if a {@link DbcmodelEditor} is used
    * and changes of the selected {@link DbcProof} in a {@link DbcmodelEditor}.
    */
   @Test
   public void testAdapter_DbcmodelEditor() throws Exception {
      SWTBotEditor editor = null;
      ProofDependenciesViewPart dependenciesViewPart = null;
      LogStartProofJobListener startProofListener = new LogStartProofJobListener();
      StartProofJob.addStartProofJobListener(startProofListener);
      String originalRuntimeExceptions = null;
      try {
         // Store original settings of KeY which requires that at least one proof was instantiated.
         if (!SymbolicExecutionUtil.isChoiceSettingInitialised()) {
            KeYEnvironment<?> environment = KeYEnvironment.load(KeYExampleUtil.getExampleProof(), null, null);
            environment.dispose();
         }
         originalRuntimeExceptions = SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
         assertNotNull(originalRuntimeExceptions);
         SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW);
         // Create and fill project if not already available
         IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject("SWTBotProofProviderAdapterFactoryTest");
         IFolder src;
         if (!project.exists()) {
            project = TestUtilsUtil.createProject("SWTBotProofProviderAdapterFactoryTest");
            src = TestUtilsUtil.createFolder(project, "src");
            BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/TwoClassesWithDiagram/test", src);
         }
         else {
            src = project.getFolder("src");
         }
         IFile modelFile = src.getFile("default.dbc");
         // Open editor
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot);
         TestUtilsUtil.openEditor(modelFile);
         editor = bot.editorByTitle(modelFile.getName());
         SWTBotTree tree = editor.bot().tree();
         tree.select(0);
         // Open dependencies view and make sure that no diagram is shown
         dependenciesViewPart = (ProofDependenciesViewPart)TestUtilsUtil.openView(ProofDependenciesViewPart.VIEW_ID);
         SWTBotView dependenciesView = bot.viewById(dependenciesViewPart.getViewSite().getId());
         assertEquals("The active editor provides no supported proof.", dependenciesView.bot().label(0).getText());
         assertNull(dependenciesViewPart.getCurrentModel());
         // Test adapter
         IEditorPart part = editor.getReference().getEditor(true);
         assertNotNull(part);
         IProofProvider provider = (IProofProvider)part.getAdapter(IProofProvider.class);
         assertNotNull(provider);
         IProofProvider providerAgain = (IProofProvider)part.getAdapter(IProofProvider.class);
         assertSame(provider, providerAgain);
         // Get proofs
         String resourceString = URI.createPlatformResourceURI(modelFile.getFullPath().toString(), true).toString();
         String modelString = "Dbc Model " + KeyDriver.ID;
         DbcModel model = (DbcModel)TestUtilsUtil.getObjectInTree(tree, resourceString, modelString);
         DbcProof firstProof = model.getProofs().get(0);
         String[] pathToFirstProof = {resourceString, modelString, "Dbc Proof " + firstProof.getObligation()};
         int[] pathToSecondProof = {0, 0, 1};
         // Start first proof
         TestUtilsUtil.selectInTree(tree, pathToFirstProof);
         assertNull(dependenciesViewPart.getCurrentModel());
         TestInteractiveProvingUtil.openProof(startProofListener, tree, pathToFirstProof);
         waitForModel(dependenciesViewPart);
         compareWithOracle(oracleDirectory, dependenciesViewPart.getCurrentModel(), "data/TwoClassesWithDiagram/oracle/FirstProof.xml");
         // Start second proof
         TestUtilsUtil.selectInTree(tree, pathToSecondProof);
         waitForNoModel(dependenciesViewPart);
         assertNull(dependenciesViewPart.getCurrentModel());
         assertEquals("The active editor provides no supported proof.", dependenciesView.bot().label(0).getText());
         TestInteractiveProvingUtil.openProof(startProofListener, tree, 1);
         waitForModel(dependenciesViewPart);
         compareWithOracle(oracleDirectory, dependenciesViewPart.getCurrentModel(), "data/TwoClassesWithDiagram/oracle/SecondProof.xml");
         // Select first proof again
         DbcModel oldModel = dependenciesViewPart.getCurrentModel();
         TestUtilsUtil.selectInTree(tree, pathToFirstProof);
         waitForModelChange(oldModel, dependenciesViewPart);
         assertNotNull(dependenciesViewPart.getCurrentModel());
         compareWithOracle(oracleDirectory, dependenciesViewPart.getCurrentModel(), "data/TwoClassesWithDiagram/oracle/FirstProof.xml");
         // Close data source connection
         IDSConnection connection = InteractiveConnectionUtil.getConnection(model);
         if (connection != null && connection.isConnected()) {
            connection.disconnect();
         }
         waitForNoModel(dependenciesViewPart);
         assertEquals("The active editor provides no supported proof.", dependenciesView.bot().label(0).getText());
      }
      finally {
         // Restore runtime option
         if (originalRuntimeExceptions != null) {
            SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalRuntimeExceptions);
         }
         // Remove listener
         StartProofJob.removeStartProofJobListener(startProofListener);
         // Close editor and view
         if (editor != null) {
            editor.close();
         }
         if (dependenciesViewPart != null) {
            TestUtilsUtil.closeView(dependenciesViewPart);
         }
      }
   }
   
   /**
    * Tests the returned adapter if a {@link DbCDiagramEditor} is used
    * and changes of the selected {@link DbcProof} in a {@link DbCDiagramEditor}.
    */
   @Test
   public void testAdapter_DiagramEditor() throws Exception {
      SWTBotGefEditor editor = null;
      ProofDependenciesViewPart dependenciesViewPart = null;
      LogStartProofJobListener startProofListener = new LogStartProofJobListener();
      StartProofJob.addStartProofJobListener(startProofListener);
      try {
         // Create and fill project if not already available
         IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject("SWTBotProofProviderAdapterFactoryTest");
         IFolder src;
         if (!project.exists()) {
            project = TestUtilsUtil.createProject("SWTBotProofProviderAdapterFactoryTest");
            src = TestUtilsUtil.createFolder(project, "src");
            BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/TwoClassesWithDiagram/test", src);
         }
         else {
            src = project.getFolder("src");
         }
         IFile diagramFile = src.getFile("default.dbc_diagram");
         // Open editor
         SWTGefBot bot = new SWTGefBot();
         TestUtilsUtil.closeWelcomeView(bot);
         TestUtilsUtil.openEditor(diagramFile);
         editor = bot.gefEditor(diagramFile.getName());
         // Open dependencies view and make sure that no diagram is shown
         dependenciesViewPart = (ProofDependenciesViewPart)TestUtilsUtil.openView(ProofDependenciesViewPart.VIEW_ID);
         SWTBotView dependenciesView = bot.viewById(dependenciesViewPart.getViewSite().getId());
         assertEquals("The active editor provides no supported proof.", dependenciesView.bot().label(0).getText());
         assertNull(dependenciesViewPart.getCurrentModel());
         // Test adapter
         IEditorPart part = editor.getReference().getEditor(true);
         assertNotNull(part);
         IProofProvider provider = (IProofProvider)part.getAdapter(IProofProvider.class);
         assertNotNull(provider);
         IProofProvider providerAgain = (IProofProvider)part.getAdapter(IProofProvider.class);
         assertSame(provider, providerAgain);
         // Get proofs
         List<SWTBotGefEditPart> proofEditParts = TestInteractiveProvingUtil.getEditPartsByModelClass(editor, DbcProof.class);
         // Start first proof
         editor.select(proofEditParts.get(0));
         assertNull(dependenciesViewPart.getCurrentModel());
         TestInteractiveProvingUtil.openProof(startProofListener, editor, proofEditParts.get(0));
         waitForModel(dependenciesViewPart);
         compareWithOracle(oracleDirectory, dependenciesViewPart.getCurrentModel(), "data/TwoClassesWithDiagram/oracle/FirstProof.xml");
         // Start second proof
         editor.select(proofEditParts.get(2));
         waitForNoModel(dependenciesViewPart);
         assertNull(dependenciesViewPart.getCurrentModel());
         assertEquals("The active editor provides no supported proof.", dependenciesView.bot().label(0).getText());
         TestInteractiveProvingUtil.openProof(startProofListener, editor, proofEditParts.get(2));
         waitForModel(dependenciesViewPart);
         compareWithOracle(oracleDirectory, dependenciesViewPart.getCurrentModel(), "data/TwoClassesWithDiagram/oracle/SecondProof.xml");
         // Select first proof again
         DbcModel oldModel = dependenciesViewPart.getCurrentModel();
         editor.select(proofEditParts.get(0));
         waitForModelChange(oldModel, dependenciesViewPart);
         assertNotNull(dependenciesViewPart.getCurrentModel());
         compareWithOracle(oracleDirectory, dependenciesViewPart.getCurrentModel(), "data/TwoClassesWithDiagram/oracle/FirstProof.xml");
         // Close data source connection
         DbcProof proof = (DbcProof)proofEditParts.get(0).part().getAdapter(DbcProof.class);
         DbcModel editorModel = DbcModelUtil.getModelRoot(proof);
         IDSConnection connection = InteractiveConnectionUtil.getConnection(editorModel);
         if (connection != null && connection.isConnected()) {
            connection.disconnect();
         }
         waitForNoModel(dependenciesViewPart);
         assertEquals("The active editor provides no supported proof.", dependenciesView.bot().label(0).getText());
      }
      finally {
         StartProofJob.removeStartProofJobListener(startProofListener);
         if (editor != null) {
            editor.close();
         }
         if (dependenciesViewPart != null) {
            TestUtilsUtil.closeView(dependenciesViewPart);
         }
      }
   }

   /**
    * Waits until a different {@link DbcModel} is provided by the given {@link ProofDependenciesViewPart}.
    * @param oldModel The current {@link DbcModel}.
    * @param dependenciesViewPart The {@link ProofDependenciesViewPart} to use.
    */
   protected void waitForModelChange(DbcModel oldModel, ProofDependenciesViewPart dependenciesViewPart) {
      long start = System.currentTimeMillis();
      while (dependenciesViewPart.getCurrentModel() == oldModel &&
             System.currentTimeMillis() - start < SWTBotPreferences.TIMEOUT) { // Timeout after some time
         TestUtilsUtil.sleep(100);
      }
      assertNotSame(oldModel, dependenciesViewPart.getCurrentModel()); // Make sure that a different or no model is provided
   }

   /**
    * Waits until no {@link DbcModel} is provided by the given {@link ProofDependenciesViewPart}.
    * @param dependenciesViewPart The {@link ProofDependenciesViewPart} to use.
    */
   protected void waitForNoModel(ProofDependenciesViewPart dependenciesViewPart) {
      long start = System.currentTimeMillis();
      while (dependenciesViewPart.getCurrentModel() != null &&
             System.currentTimeMillis() - start < SWTBotPreferences.TIMEOUT) { // Timeout after some time
         TestUtilsUtil.sleep(100);
      }
      assertNull(dependenciesViewPart.getCurrentModel()); // Make sure that no model is provided
   }

   /**
    * Waits until a {@link DbcModel} is provided by the given {@link ProofDependenciesViewPart}.
    * @param dependenciesViewPart The {@link ProofDependenciesViewPart} to use.
    */
   protected void waitForModel(ProofDependenciesViewPart dependenciesViewPart) {
      long start = System.currentTimeMillis();
      while (dependenciesViewPart.getCurrentModel() == null &&
             System.currentTimeMillis() - start < SWTBotPreferences.TIMEOUT) { // Timeout after some time
         TestUtilsUtil.sleep(100);
      }
      assertNotNull(dependenciesViewPart.getCurrentModel()); // Make sure that a model is provided
   }
}