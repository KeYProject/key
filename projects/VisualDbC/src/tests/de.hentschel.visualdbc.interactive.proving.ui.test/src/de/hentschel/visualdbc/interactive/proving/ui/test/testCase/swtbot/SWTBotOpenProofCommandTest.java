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

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase.swtbot;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.emf.common.command.Command;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.edit.command.SetCommand;
import org.eclipse.emf.edit.domain.EditingDomain;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.gef.finder.SWTGefBot;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditPart;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProvableReference;
import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcProofStatus;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.dbcmodel.presentation.DbcmodelEditor;
import de.hentschel.visualdbc.interactive.proving.ui.command.OpenProofCommand;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.job.StartProofJob;
import de.hentschel.visualdbc.interactive.proving.ui.test.Activator;
import de.hentschel.visualdbc.interactive.proving.ui.test.model.ExecutableProof;
import de.hentschel.visualdbc.interactive.proving.ui.test.model.LoggingMethod;
import de.hentschel.visualdbc.interactive.proving.ui.test.model.LoggingOperationContract;
import de.hentschel.visualdbc.interactive.proving.ui.test.model.SimpleProofModelDriver;
import de.hentschel.visualdbc.interactive.proving.ui.test.util.TestInteractiveProvingUtil;
import de.hentschel.visualdbc.interactive.proving.ui.test.util.TestInteractiveProvingUtil.LogStartProofJobListener;
import de.hentschel.visualdbc.interactive.proving.ui.util.DbcModelUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.FinderUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveConnectionUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveProvingPreferences;
import de.hentschel.visualdbc.interactive.proving.ui.util.ProofUtil;

/**
 * Tests for {@link OpenProofCommand} and also {@link ProofUtil}.
 * @author Martin Hentschel
 */
public class SWTBotOpenProofCommandTest extends TestCase {
   /**
    * Listens for opened interactive proofs and logs the starts internally.
    */
   private LogStartProofJobListener startProofListener = new LogStartProofJobListener();
   
   /**
    * {@inheritDoc}
    */
   @Before
   @Override
   public void setUp() throws Exception {
      StartProofJob.addStartProofJobListener(startProofListener);
   }

   /**
    * {@inheritDoc}
    */
   @After
   @Override
   public void tearDown() throws Exception {
      StartProofJob.removeStartProofJobListener(startProofListener);
   }

   /**
    * Tests opening proofs in the following scenarios:
    * <ul>
    *    <li>Open proof on operation contract</li>
    *    <li>Open proof on operation contract again</li>
    *    <li>Open proof on other operation contract</li>
    *    <li>Open proof on method</li>
    *    <li>Open proof with invalid obligation</li>
    *    <li>Open proof without target</li>
    *    <li>Finish multiple proofs</li>
    *    <li>Adding multiple references to a proof</li>
    *    <li>Proof resets: status</li>
    *    <li>Proof resets: references</li>
    * </ul>
    */
   @Test
   public void testOpenProofs_ModelEditor_withResets() {
      doTestOpenProofs_ModelEditor(true);
   }
   
   /**
    * Tests opening proofs in the following scenarios:
    * <ul>
    *    <li>Open proof on operation contract</li>
    *    <li>Open proof on operation contract again</li>
    *    <li>Open proof on other operation contract</li>
    *    <li>Open proof on method</li>
    *    <li>Open proof with invalid obligation</li>
    *    <li>Open proof without target</li>
    *    <li>Finish multiple proofs</li>
    *    <li>Adding multiple references to a proof</li>
    *    <li>Proof resets: status</li>
    *    <li>Proof resets: references</li>
    * </ul>
    */
   @Test
   public void testOpenProofs_ModelEditor_noResets() {
      doTestOpenProofs_ModelEditor(false);
   }

   /**
    * Executes the tests for {@link #testOpenProofs_ModelEditor_noResets()}
    * and {@link #testOpenProofs_ModelEditor_withResets()}
    * @param allowProofResets Allow proof resets?
    */   
   protected void doTestOpenProofs_ModelEditor(boolean allowProofResets) {
      boolean oldAutomatedMode = ErrorDialog.AUTOMATED_MODE;
      boolean oldResetProofs = InteractiveProvingPreferences.isResetProofIfNewOpened();
      try {
         // Set reset setting
         InteractiveProvingPreferences.setResetProofIfNewOpened(allowProofResets);
         // Allow error dialogs
         ErrorDialog.AUTOMATED_MODE = false;
         // Create and fill project
         IProject project = TestUtilsUtil.createProject("SWTBotOpenProofCommandTest_testOpenProofs_ModelEditor_" + allowProofResets);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/SimpleProofModelDifferentContainment", project);
         final IFile modelFile = project.getFile("SimpleProofModel.dbc");
         // Open editor
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot);
         TestUtilsUtil.openEditor(modelFile);
         SWTBotEditor editor = bot.editorByTitle(modelFile.getName());
         SWTBotTree tree = editor.bot().tree();
         tree.select(0);
         // Make sure that no connection is established
         String resourceString = URI.createPlatformResourceURI(modelFile.getFullPath().toString(), true).toString();
         String modelString = "Dbc Model de.hentschel.visualdbc.dbcmodel.diagram.custom.test.simpleProofModel";
         DbcModel model = (DbcModel)TestUtilsUtil.getObjectInTree(tree, resourceString, modelString);
         DbcClass mCDemo = (DbcClass)model.getType("MCDemo");
         DbcMethod inc = mCDemo.getMethod("inc(x : int)");
         DbcOperationContract c0 = inc.getOperationContracts().get(0);
         DbcMethod init = mCDemo.getMethod("init(u : int)");
         DbcOperationContract c1 = init.getOperationContracts().get(0);
         assertNotNull(model);
         assertFalse(InteractiveConnectionUtil.isOpened(model));
         // Get proofs
         String mCDemoString = "Dbc Class MCDemo";
         String[] c1EnsuresPostPath = {resourceString, modelString, mCDemoString, "Dbc Proof EnsuresPost"};
         DbcProof c1EnsuresPost = (DbcProof)TestUtilsUtil.getObjectInTree(tree, c1EnsuresPostPath);
         assertEquals(c1, c1EnsuresPost.getTarget());
         assertEquals("EnsuresPost", c1EnsuresPost.getObligation());
         String[] c0EnsuresPostPath = {resourceString, modelString, "Dbc Proof EnsuresPost"};
         DbcProof c0EnsuresPost = (DbcProof)TestUtilsUtil.getObjectInTree(tree, c0EnsuresPostPath);
         assertEquals(c0, c0EnsuresPost.getTarget());
         assertEquals("EnsuresPost", c0EnsuresPost.getObligation());
         String[] incPreservesInvPath = {resourceString, modelString, mCDemoString, "Dbc Proof PreservesInv"};
         DbcProof incPreservesInv = (DbcProof)TestUtilsUtil.getObjectInTree(tree, incPreservesInvPath);
         assertEquals(inc, incPreservesInv.getTarget());
         assertEquals("PreservesInv", incPreservesInv.getObligation());
         String[] incInvalidPath = {resourceString, modelString, mCDemoString, "Dbc Proof InvalidObligation"};
         DbcProof incInvalid = (DbcProof)TestUtilsUtil.getObjectInTree(tree, incInvalidPath);
         assertEquals(inc, incInvalid.getTarget());
         assertEquals("InvalidObligation", incInvalid.getObligation());
         String[] noTargetPath = {resourceString, modelString, mCDemoString, "Dbc Proof NoProofTarget"};
         DbcProof noTarget = (DbcProof)TestUtilsUtil.getObjectInTree(tree, noTargetPath);
         assertNull(noTarget.getTarget());
         assertEquals("NoProofTarget", noTarget.getObligation());
         String[] c1RespectsModifiesPath = {resourceString, modelString, mCDemoString, "Dbc Proof RespectsModifies"};
         DbcProof c1RespectsModifies = (DbcProof)TestUtilsUtil.getObjectInTree(tree, c1RespectsModifiesPath);
         assertEquals(c1, c1RespectsModifies.getTarget());
         assertEquals("RespectsModifies", c1RespectsModifies.getObligation());
         // Open proof: EnsuresPost on c1
         TestInteractiveProvingUtil.openProof(startProofListener, tree, c1EnsuresPostPath);
         compareOpenProofCalls(model, "EnsuresPost", null, null);
         assertEquals(DbcProofStatus.OPEN, c1EnsuresPost.getStatus());
         // Open proof again: EnsuresPost on c1
         TestInteractiveProvingUtil.openProof(startProofListener, tree, c1EnsuresPostPath);
         compareOpenProofCalls(model, "EnsuresPost", null, null);
         // Open proof: RespectsModifies on c1
         TestInteractiveProvingUtil.openProof(startProofListener, tree, c1RespectsModifiesPath);
         compareOpenProofCalls(model, "RespectsModifies", null, null);
         // Open proof: EnsuresPost on c0
         TestInteractiveProvingUtil.openProof(startProofListener, tree, c0EnsuresPostPath);
         compareOpenProofCalls(model, null, "EnsuresPost", null);
         // Open proof: EnsuresPost on c1 and c0
         SWTBotTreeItem firstItem = TestUtilsUtil.selectInTree(tree, c0EnsuresPostPath);
         SWTBotTreeItem secondItem = TestUtilsUtil.selectInTree(tree, c1EnsuresPostPath);
         tree.select(firstItem, secondItem);
         TestInteractiveProvingUtil.openProof(startProofListener, tree, 2);
         compareOpenProofCalls(model, "EnsuresPost", "EnsuresPost", null);
         // Open proof: PreservesInv on inc
         TestInteractiveProvingUtil.openProof(startProofListener, tree, incPreservesInvPath);
         compareOpenProofCalls(model, null, null, "PreservesInv");
         // Open proof: invalid on inc
         TestInteractiveProvingUtil.openProof(startProofListener, tree, incInvalidPath);
         compareOpenProofCalls(model, null, null, null);
         SWTBotShell errorShell = bot.shell("Problem Occurred");
         assertEquals("The obligation \"InvalidObligation\" is invalid.\nValid obligations are:\n -PreservesInv", errorShell.bot().label(2).getText());
         errorShell.bot().button("OK").click();
         // Open proof: noTarget
         TestInteractiveProvingUtil.openProof(startProofListener, tree, noTargetPath);
         compareOpenProofCalls(model, null, null, null);
         errorShell = bot.shell("Problem Occurred");
         assertEquals("Proof target not defined.", errorShell.bot().label(2).getText());
         errorShell.bot().button("OK").click();
         // Get data source model instances
         IDSConnection connection = InteractiveConnectionUtil.openConnection(model, null);
         IDSClass dsMCDemo = connection.getClass("MCDemo");
         LoggingMethod dsInc = (LoggingMethod)dsMCDemo.getMethod("inc(x : int)");
         LoggingOperationContract dsC0 = (LoggingOperationContract)dsInc.getOperationContracts().get(0);
         LoggingMethod dsInit = (LoggingMethod)dsMCDemo.getMethod("init(u : int)");
         LoggingOperationContract dsC1 = (LoggingOperationContract)dsInit.getOperationContracts().get(0);
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         // Close proof: c1EnsuresPost
         ((ExecutableProof)dsC1.getInteractiveProof(c1EnsuresPost.getObligation())).closeProof();
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         // Close proof again: c1EnsuresPost
         ((ExecutableProof)dsC1.getInteractiveProof(c1EnsuresPost.getObligation())).closeProof();
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         // Close proof again: c1RespectsModifies
         ((ExecutableProof)dsC1.getInteractiveProof(c1RespectsModifies.getObligation())).closeProof();
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                  DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         }
         // Close proof again: c0EnsuresPost
         ((ExecutableProof)dsC0.getInteractiveProof(c0EnsuresPost.getObligation())).closeProof();
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         }
         // Close proof again: incPreservesInv
         ((ExecutableProof)dsInc.getInteractiveProof(incPreservesInv.getObligation())).closeProof();
         compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                           DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         // Test initial references of dsC1
         IDbcFinder finder = FinderUtil.getDbcFinder(connection, model);
         assertNotNull(finder);
         List<IDSProvableReference> allowedReferences = new LinkedList<IDSProvableReference>();
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Add reference dsC1 to dsInc
         allowedReferences.add(new MemoryProvableReference(dsInc, "KindA"));
         ((ExecutableProof)dsC1.getInteractiveProof(c1EnsuresPost.getObligation())).addReferences(new MemoryProvableReference(dsInc, "KindA"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Add reference dsC1 to dsInit
         allowedReferences.add(new MemoryProvableReference(dsInit, "KindB"));
         ((ExecutableProof)dsC1.getInteractiveProof(c1EnsuresPost.getObligation())).addReferences(new MemoryProvableReference(dsInit, "KindB"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Add reference dsC1 to dsInit with other kind
         allowedReferences.add(new MemoryProvableReference(dsInit, "KindC"));
         ((ExecutableProof)dsC1.getInteractiveProof(c1EnsuresPost.getObligation())).addReferences(new MemoryProvableReference(dsInit, "KindC"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Add multiple references
         allowedReferences.add(new MemoryProvableReference(dsInit, "KindD"));
         allowedReferences.add(new MemoryProvableReference(dsInc, "KindE"));
         ((ExecutableProof)dsC1.getInteractiveProof(c1EnsuresPost.getObligation())).addReferences(new MemoryProvableReference(dsInit, "KindC"), new MemoryProvableReference(dsInit, "KindD"), new MemoryProvableReference(dsInc, "KindE"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Remove reference
         allowedReferences.remove(new MemoryProvableReference(dsInit, "KindD"));
         ((ExecutableProof)dsC1.getInteractiveProof(c1EnsuresPost.getObligation())).removeReferences(new MemoryProvableReference(dsInit, "KindD"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);         
         // Remove multiple references
         allowedReferences.remove(new MemoryProvableReference(dsInit, "KindB"));
         allowedReferences.remove(new MemoryProvableReference(dsInc, "KindA"));
         ((ExecutableProof)dsC1.getInteractiveProof(c1EnsuresPost.getObligation())).removeReferences(new MemoryProvableReference(dsInit, "KindD"), new MemoryProvableReference(dsInit, "KindB"), new MemoryProvableReference(dsInc, "KindA"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Test proof resets based on the status values
         IDSFinder dsFinder = FinderUtil.getDSFinder(connection);
         assertNotNull(dsFinder);
         EditingDomain domain = ((DbcmodelEditor)editor.getReference().getEditor(true)).getEditingDomain();
         doTestStatusBasedRest(domain, model, tree, c1EnsuresPost, c1EnsuresPostPath, allowProofResets, dsFinder, DbcProofStatus.FAILED);
         doTestStatusBasedRest(domain, model, tree, c1EnsuresPost, c1EnsuresPostPath, allowProofResets, dsFinder, DbcProofStatus.OPEN);
         doTestStatusBasedRest(domain, model, tree, c1EnsuresPost, c1EnsuresPostPath, allowProofResets, dsFinder, DbcProofStatus.FULFILLED);
         // Test proof resets based on references
         doTestReferenceBasedTest(domain, model, tree, c1EnsuresPost, c1EnsuresPostPath, allowProofResets, dsFinder, c1EnsuresPost.getTarget());
         // Test opening a proof with initial references
         DbcProof proof = c0EnsuresPost;
         IDSProvable dsProvable = dsFinder.findProvable(proof.getTarget());
         if (dsProvable instanceof LoggingMethod) {
            ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
            ((LoggingMethod)dsProvable).setInitialReferenceToAdd(new MemoryProvableReference(dsProvable, "Initial Reference"));
         }
         else if (dsProvable instanceof LoggingOperationContract) {
            ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
            ((LoggingOperationContract)dsProvable).setInitialReferenceToAdd(new MemoryProvableReference(dsProvable, "Initial Reference"));
         }
         assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
         TestInteractiveProvingUtil.openProof(startProofListener, tree, c0EnsuresPostPath);
         compareOpenProofCalls(model, null, "EnsuresPost", null);
         assertEquals(1, proof.getProofReferences().size());
         assertEquals(proof.getTarget(), proof.getProofReferences().get(0).getTarget());
         assertEquals("Initial Reference", proof.getProofReferences().get(0).getKind());
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      catch (CoreException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      finally {
         ErrorDialog.AUTOMATED_MODE = oldAutomatedMode;
         InteractiveProvingPreferences.setResetProofIfNewOpened(oldResetProofs);
         // Close editor
         new SWTWorkbenchBot().closeAllEditors();
      }
   }
   
   /**
    * Tests the resetting of proof references.
    * @param domain The {@link EditingDomain} to use.
    * @param model The {@link DbcModel} to use.
    * @param tree The {@link SWTBotTree} to use.
    * @param proof The proof to check.
    * @param proofPath The path to the proof.
    * @param allowProofResets Allow proof resets?
    * @param dsFinder The {@link IDSFinder} to use.
    * @param target The target to use for test references.
    * @throws DSException Occurred Exception.
    */
   protected void doTestReferenceBasedTest(EditingDomain domain, 
                                           DbcModel model, 
                                           SWTBotTree tree, 
                                           DbcProof proof, 
                                           String[] proofPath, 
                                           boolean allowProofResets, 
                                           IDSFinder dsFinder, 
                                           IDbCProvable target) throws DSException {
      // Remove already opened proof
      IDSProvable dsProvable = dsFinder.findProvable(proof.getTarget());
      if (dsProvable instanceof LoggingMethod) {
         ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
      }
      else if (dsProvable instanceof LoggingOperationContract) {
         ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
      }
      assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Set initial references
      ProofUtil.createReference(domain, proof, target, "TestReferenceToDelete");
      assertFalse(proof.getProofReferences().isEmpty());
      // Open proof
      TestInteractiveProvingUtil.openProof(startProofListener, tree, proofPath);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      if (allowProofResets) {
         assertTrue(proof.getProofReferences().isEmpty());
      }
      else {
         assertFalse(proof.getProofReferences().isEmpty());
      }
      assertTrue(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Open proof again (proof now opened, no reset required)
      ProofUtil.createReference(domain, proof, target, "TestReferenceToDelete");
      TestInteractiveProvingUtil.openProof(startProofListener, tree, proofPath);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      assertFalse(proof.getProofReferences().isEmpty());
      // Remove prove
      if (dsProvable instanceof LoggingMethod) {
         ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
      }
      else if (dsProvable instanceof LoggingOperationContract) {
         ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
      }
      assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Open proof again
      TestInteractiveProvingUtil.openProof(startProofListener, tree, proofPath);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      if (allowProofResets) {
         assertTrue(proof.getProofReferences().isEmpty());
      }
      else {
         assertFalse(proof.getProofReferences().isEmpty());
      }
      assertTrue(dsProvable.hasInteractiveProof(proof.getObligation()));
   }
   
   /**
    * Tests status based resets.
    * @param domain The {@link EditingDomain} to use.
    * @param model The {@link DbcModel} to use.
    * @param tree The {@link SWTBotTree} to use.
    * @param proof The proof to test.
    * @param proofPath The path to the proof inside the tree.
    * @param allowProofResets Allow proof resets?
    * @param dsFinder The {@link IDSFinder} to use.
    * @param statusToSet The initial status to test.
    * @throws DSException Occurred Exception
    */
   protected void doTestStatusBasedRest(EditingDomain domain, 
                                        DbcModel model, 
                                        SWTBotTree tree, 
                                        DbcProof proof, 
                                        String[] proofPath, 
                                        boolean allowProofResets, 
                                        IDSFinder dsFinder, 
                                        DbcProofStatus statusToSet) throws DSException {
      // Remove already opened proof
      IDSProvable dsProvable = dsFinder.findProvable(proof.getTarget());
      if (dsProvable instanceof LoggingMethod) {
         ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
      }
      else if (dsProvable instanceof LoggingOperationContract) {
         ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
      }
      assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Set initial status
      Command setStatusCmd = SetCommand.create(domain, proof, DbcmodelPackage.Literals.DBC_PROOF__STATUS, statusToSet);
      domain.getCommandStack().execute(setStatusCmd);
      assertEquals(statusToSet, proof.getStatus());
      // Open proof
      TestInteractiveProvingUtil.openProof(startProofListener, tree, proofPath);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      if (allowProofResets) {
         assertEquals(DbcProofStatus.OPEN, proof.getStatus());
      }
      else {
         assertEquals(statusToSet, proof.getStatus());
      }
      assertTrue(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Open proof again (proof now opened, no reset required)
      setStatusCmd = SetCommand.create(domain, proof, DbcmodelPackage.Literals.DBC_PROOF__STATUS, statusToSet);
      domain.getCommandStack().execute(setStatusCmd);
      TestInteractiveProvingUtil.openProof(startProofListener, tree, proofPath);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      assertEquals(statusToSet, proof.getStatus());
      // Remove prove
      if (dsProvable instanceof LoggingMethod) {
         ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
      }
      else if (dsProvable instanceof LoggingOperationContract) {
         ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
      }
      assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Open proof again
      TestInteractiveProvingUtil.openProof(startProofListener, tree, proofPath);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      if (allowProofResets) {
         assertEquals(DbcProofStatus.OPEN, proof.getStatus());
      }
      else {
         assertEquals(statusToSet, proof.getStatus());
      }
      assertTrue(dsProvable.hasInteractiveProof(proof.getObligation()));
   }

   /**
    * Tests opening proofs in the following scenarios:
    * <ul>
    *    <li>Open proof on operation contract</li>
    *    <li>Open proof on operation contract again</li>
    *    <li>Open proof on other operation contract</li>
    *    <li>Open proof on method</li>
    *    <li>Open proof with invalid obligation</li>
    *    <li>Open proof without target</li>
    *    <li>Finish multiple proofs</li>
    *    <li>Adding multiple references to a proof</li>
    *    <li>Proof resets: status</li>
    *    <li>Proof resets: references</li>
    * </ul>
    */
   @Test
   public void testOpenProofs_DiagramEditor_withResets() {
      doTestOpenProofs_DiagramEditor(true);
   }
   
   /**
    * Tests opening proofs in the following scenarios:
    * <ul>
    *    <li>Open proof on operation contract</li>
    *    <li>Open proof on operation contract again</li>
    *    <li>Open proof on other operation contract</li>
    *    <li>Open proof on method</li>
    *    <li>Open proof with invalid obligation</li>
    *    <li>Open proof without target</li>
    *    <li>Finish multiple proofs</li>
    *    <li>Adding multiple references to a proof</li>
    *    <li>Proof resets: status</li>
    *    <li>Proof resets: references</li>
    * </ul>
    */
   @Test
   public void testOpenProofs_DiagramEditor_noResets() {
      doTestOpenProofs_DiagramEditor(false);
   }

   /**
    * Executes the tests for {@link #testOpenProofs_DiagramEditor_noResets()}
    * and {@link #testOpenProofs_DiagramEditor_withResets()}
    * @param allowProofResets Allow proof resets?
    */
   protected void doTestOpenProofs_DiagramEditor(boolean allowProofResets) {
      boolean oldAutomatedMode = ErrorDialog.AUTOMATED_MODE;
      boolean oldResetProofs = InteractiveProvingPreferences.isResetProofIfNewOpened();
      try {
         // Set reset setting
         InteractiveProvingPreferences.setResetProofIfNewOpened(allowProofResets);
         // Allow error dialogs
         ErrorDialog.AUTOMATED_MODE = false;
         // Create and fill project
         IProject project = TestUtilsUtil.createProject("SWTBotOpenProofCommandTest_testOpenProofs_DiagramEditor_" + allowProofResets);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/SimpleProofModel", project);
         final IFile diagramFile = project.getFile("SimpleProofModel.dbc_diagram");
         // Open editor
         SWTGefBot bot = new SWTGefBot();
         TestUtilsUtil.closeWelcomeView(bot);
         TestUtilsUtil.openEditor(diagramFile);
         SWTBotGefEditor editor = bot.gefEditor(diagramFile.getName());
         // Make sure that no connection is established
         DbcModel model = DbcModelUtil.getModelRoot(TestInteractiveProvingUtil.getEditModel(editor.mainEditPart()));
         DbcClass mCDemo = (DbcClass)model.getType("MCDemo");
         DbcMethod inc = mCDemo.getMethod("inc(x : int)");
         DbcOperationContract c0 = inc.getOperationContracts().get(0);
         DbcMethod init = mCDemo.getMethod("init(u : int)");
         DbcOperationContract c1 = init.getOperationContracts().get(0);
         assertNotNull(model);
         assertFalse(InteractiveConnectionUtil.isOpened(model));
         // Get proofs
         List<SWTBotGefEditPart> proofEditParts = TestInteractiveProvingUtil.getEditPartsByModelClass(editor, DbcProof.class);
         SWTBotGefEditPart c1EnsuresPost = proofEditParts.get(0);
         assertEquals(c1, ((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getTarget());
         assertEquals("EnsuresPost", ((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getObligation());
         SWTBotGefEditPart c0EnsuresPost = proofEditParts.get(2);
         assertEquals(c0, ((DbcProof)TestInteractiveProvingUtil.getEditModel(c0EnsuresPost)).getTarget());
         assertEquals("EnsuresPost", ((DbcProof)TestInteractiveProvingUtil.getEditModel(c0EnsuresPost)).getObligation());
         SWTBotGefEditPart incPreservesInv = proofEditParts.get(4);
         assertEquals(inc, ((DbcProof)TestInteractiveProvingUtil.getEditModel(incPreservesInv)).getTarget());
         assertEquals("PreservesInv", ((DbcProof)TestInteractiveProvingUtil.getEditModel(incPreservesInv)).getObligation());
         SWTBotGefEditPart incInvalid = proofEditParts.get(6);
         assertEquals(inc, ((DbcProof)TestInteractiveProvingUtil.getEditModel(incInvalid)).getTarget());
         assertEquals("InvalidObligation", ((DbcProof)TestInteractiveProvingUtil.getEditModel(incInvalid)).getObligation());
         SWTBotGefEditPart noTarget = proofEditParts.get(8);
         assertNull(((DbcProof)TestInteractiveProvingUtil.getEditModel(noTarget)).getTarget());
         assertEquals("NoProofTarget", ((DbcProof)TestInteractiveProvingUtil.getEditModel(noTarget)).getObligation());
         SWTBotGefEditPart c1RespectsModifies = proofEditParts.get(10);
         assertEquals(c1, ((DbcProof)TestInteractiveProvingUtil.getEditModel(c1RespectsModifies)).getTarget());
         assertEquals("RespectsModifies", ((DbcProof)TestInteractiveProvingUtil.getEditModel(c1RespectsModifies)).getObligation());
         // Open proof: EnsuresPost on c1
         TestInteractiveProvingUtil.openProof(startProofListener, editor, c1EnsuresPost);
         compareOpenProofCalls(model, "EnsuresPost", null, null);
         // Open proof again: EnsuresPost on c1
         TestInteractiveProvingUtil.openProof(startProofListener, editor, c1EnsuresPost);
         compareOpenProofCalls(model, "EnsuresPost", null, null);
         // Open proof: RespectsModifies on c1
         TestInteractiveProvingUtil.openProof(startProofListener, editor, c1RespectsModifies);
         compareOpenProofCalls(model, "RespectsModifies", null, null);
         // Open proof: EnsuresPost on c0
         TestInteractiveProvingUtil.openProof(startProofListener, editor, c0EnsuresPost);
         compareOpenProofCalls(model, null, "EnsuresPost", null);
         // Open proof: EnsuresPost on c1 and c0
         editor.select(c0EnsuresPost, c1EnsuresPost);
         TestInteractiveProvingUtil.openProof(startProofListener, editor, 2);
         compareOpenProofCalls(model, "EnsuresPost", "EnsuresPost", null);
         // Open proof: PreservesInv on inc
         TestInteractiveProvingUtil.openProof(startProofListener, editor, incPreservesInv);
         compareOpenProofCalls(model, null, null, "PreservesInv");
         // Open proof: invalid on inc
         TestInteractiveProvingUtil.openProof(startProofListener, editor, incInvalid);
         compareOpenProofCalls(model, null, null, null);
         SWTBotShell errorShell = bot.shell("Problem Occurred");
         assertEquals("The obligation \"InvalidObligation\" is invalid.\nValid obligations are:\n -PreservesInv", errorShell.bot().label(2).getText());
         errorShell.bot().button("OK").click();
         // Open proof: noTarget
         TestInteractiveProvingUtil.openProof(startProofListener, editor, noTarget);
         compareOpenProofCalls(model, null, null, null);
         errorShell = bot.shell("Problem Occurred");
         assertEquals("Proof target not defined.", errorShell.bot().label(2).getText());
         errorShell.bot().button("OK").click();
         // Get data source model instances
         IDSConnection connection = InteractiveConnectionUtil.openConnection(model, null);
         IDSClass dsMCDemo = connection.getClass("MCDemo");
         LoggingMethod dsInc = (LoggingMethod)dsMCDemo.getMethod("inc(x : int)");
         LoggingOperationContract dsC0 = (LoggingOperationContract)dsInc.getOperationContracts().get(0);
         LoggingMethod dsInit = (LoggingMethod)dsMCDemo.getMethod("init(u : int)");
         LoggingOperationContract dsC1 = (LoggingOperationContract)dsInit.getOperationContracts().get(0);
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         // Close proof: c1EnsuresPost
         ((ExecutableProof)dsC1.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getObligation())).closeProof();
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         // Close proof again: c1EnsuresPost
         ((ExecutableProof)dsC1.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getObligation())).closeProof();
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN);
         }
         // Close proof again: c1RespectsModifies
         ((ExecutableProof)dsC1.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c1RespectsModifies)).getObligation())).closeProof();
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         }
         // Close proof again: c0EnsuresPost
         ((ExecutableProof)dsC0.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c0EnsuresPost)).getObligation())).closeProof();
         if (allowProofResets) {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         }
         else {
            compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                              DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FAILED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         }
         // Close proof again: incPreservesInv
         ((ExecutableProof)dsInc.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(incPreservesInv)).getObligation())).closeProof();
         compareProofStati(c1EnsuresPost, c0EnsuresPost, incPreservesInv, incInvalid, noTarget, c1RespectsModifies, 
                           DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED, DbcProofStatus.OPEN, DbcProofStatus.FULFILLED, DbcProofStatus.FULFILLED);
         // Test initial references of dsC1
         IDbcFinder finder = FinderUtil.getDbcFinder(connection, model);
         assertNotNull(finder);
         List<IDSProvableReference> allowedReferences = new LinkedList<IDSProvableReference>();
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Add reference dsC1 to dsInc
         allowedReferences.add(new MemoryProvableReference(dsInc, "KindA"));
         ((ExecutableProof)dsC1.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getObligation())).addReferences(new MemoryProvableReference(dsInc, "KindA"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Add reference dsC1 to dsInit
         allowedReferences.add(new MemoryProvableReference(dsInit, "KindB"));
         ((ExecutableProof)dsC1.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getObligation())).addReferences(new MemoryProvableReference(dsInit, "KindB"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Add reference dsC1 to dsInit with other kind
         allowedReferences.add(new MemoryProvableReference(dsInit, "KindC"));
         ((ExecutableProof)dsC1.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getObligation())).addReferences(new MemoryProvableReference(dsInit, "KindC"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Add multiple references
         allowedReferences.add(new MemoryProvableReference(dsInit, "KindD"));
         allowedReferences.add(new MemoryProvableReference(dsInc, "KindE"));
         ((ExecutableProof)dsC1.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getObligation())).addReferences(new MemoryProvableReference(dsInit, "KindC"), new MemoryProvableReference(dsInit, "KindD"), new MemoryProvableReference(dsInc, "KindE"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);
         // Remove reference
         allowedReferences.remove(new MemoryProvableReference(dsInit, "KindD"));
         ((ExecutableProof)dsC1.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getObligation())).removeReferences(new MemoryProvableReference(dsInit, "KindD"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);         
         // Remove multiple references
         allowedReferences.remove(new MemoryProvableReference(dsInit, "KindB"));
         allowedReferences.remove(new MemoryProvableReference(dsInc, "KindA"));
         ((ExecutableProof)dsC1.getInteractiveProof(((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost)).getObligation())).removeReferences(new MemoryProvableReference(dsInit, "KindD"), new MemoryProvableReference(dsInit, "KindB"), new MemoryProvableReference(dsInc, "KindA"));
         compareProofReferences(finder, c1EnsuresPost, allowedReferences);         
         // Test proof resets based on the status values
         IDSFinder dsFinder = FinderUtil.getDSFinder(connection);
         assertNotNull(dsFinder);
         EditingDomain domain = ((DbCDiagramEditor)editor.getReference().getEditor(true)).getEditingDomain();
         doTestStatusBasedRest(domain, model, editor, c1EnsuresPost, allowProofResets, dsFinder, DbcProofStatus.FAILED);
         doTestStatusBasedRest(domain, model, editor, c1EnsuresPost, allowProofResets, dsFinder, DbcProofStatus.OPEN);
         doTestStatusBasedRest(domain, model, editor, c1EnsuresPost, allowProofResets, dsFinder, DbcProofStatus.FULFILLED);
         // Test proof resets based on references
         doTestReferenceBasedTest(model, editor, c1EnsuresPost, allowProofResets, dsFinder, ((DbcProof)c1EnsuresPost.part().getAdapter(EObject.class)).getTarget());
         // Test opening a proof with initial references
         DbcProof proof = (DbcProof)c0EnsuresPost.part().getAdapter(EObject.class);
         IDSProvable dsProvable = dsFinder.findProvable(proof.getTarget());
         if (dsProvable instanceof LoggingMethod) {
            ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
            ((LoggingMethod)dsProvable).setInitialReferenceToAdd(new MemoryProvableReference(dsProvable, "Initial Reference"));
         }
         else if (dsProvable instanceof LoggingOperationContract) {
            ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
            ((LoggingOperationContract)dsProvable).setInitialReferenceToAdd(new MemoryProvableReference(dsProvable, "Initial Reference"));
         }
         assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
         TestInteractiveProvingUtil.openProof(startProofListener, editor, c0EnsuresPost);
         compareOpenProofCalls(model, null, "EnsuresPost", null);
         assertEquals(1, proof.getProofReferences().size());
         assertEquals(proof.getTarget(), proof.getProofReferences().get(0).getTarget());
         assertEquals("Initial Reference", proof.getProofReferences().get(0).getKind());
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      catch (CoreException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      finally {
         ErrorDialog.AUTOMATED_MODE = oldAutomatedMode;
         InteractiveProvingPreferences.setResetProofIfNewOpened(oldResetProofs);
         // Close editor
         new SWTWorkbenchBot().closeAllEditors();
      }
   }

   /**
    * Tests reference based resets.
    * @param model The {@link DbcModel} to use.
    * @param editor The {@link SWTBotGefEditor} to use.
    * @param proofEditPart The proof to test.
    * @param allowProofResets Allow proof resets?
    * @param dsFinder The {@link IDSFinder} to use.
    * @param target The target to use for test references.
    * @throws DSException Occurred Exception.
    */
   protected void doTestReferenceBasedTest(DbcModel model, 
                                           SWTBotGefEditor editor, 
                                           SWTBotGefEditPart proofEditPart, 
                                           boolean allowProofResets, 
                                           IDSFinder dsFinder, 
                                           IDbCProvable target) throws DSException {
      // Remove already opened proof
      DbcProof proof = (DbcProof)proofEditPart.part().getAdapter(EObject.class);
      IDSProvable dsProvable = dsFinder.findProvable(proof.getTarget());
      if (dsProvable instanceof LoggingMethod) {
         ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
      }
      else if (dsProvable instanceof LoggingOperationContract) {
         ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
      }
      assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Set initial references
      ProofUtil.createReference((ShapeNodeEditPart)proofEditPart.part(), target, "TestReferenceToDelete");
      assertFalse(proof.getProofReferences().isEmpty());
      // Open proof
      TestInteractiveProvingUtil.openProof(startProofListener, editor, proofEditPart);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      if (allowProofResets) {
         assertTrue(proof.getProofReferences().isEmpty());
      }
      else {
         assertFalse(proof.getProofReferences().isEmpty());
      }
      assertTrue(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Open proof again (proof now opened, no reset required)
      ProofUtil.createReference((ShapeNodeEditPart)proofEditPart.part(), target, "TestReferenceToDelete");
      TestInteractiveProvingUtil.openProof(startProofListener, editor, proofEditPart);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      assertFalse(proof.getProofReferences().isEmpty());
      // Remove prove
      if (dsProvable instanceof LoggingMethod) {
         ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
      }
      else if (dsProvable instanceof LoggingOperationContract) {
         ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
      }
      assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Open proof again
      TestInteractiveProvingUtil.openProof(startProofListener, editor, proofEditPart);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      if (allowProofResets) {
         assertTrue(proof.getProofReferences().isEmpty());
      }
      else {
         assertFalse(proof.getProofReferences().isEmpty());
      }
      assertTrue(dsProvable.hasInteractiveProof(proof.getObligation()));
   }
   
   /**
    * Test status based resets.
    * @param domain The {@link EditingDomain} to use.
    * @param model The {@link DbcModel} to use.
    * @param editor The {@link SWTBotGefEditor} to use.
    * @param proofEditPart The proof edit part.
    * @param allowProofResets Allow proof resets?
    * @param dsFinder The {@link IDSFinder} to use.
    * @param statusToSet The initial status to test.
    * @throws DSException Occurred Exception
    */
   protected void doTestStatusBasedRest(EditingDomain domain, 
                                        DbcModel model, 
                                        SWTBotGefEditor editor, 
                                        SWTBotGefEditPart proofEditPart, 
                                        boolean allowProofResets, 
                                        IDSFinder dsFinder, 
                                        DbcProofStatus statusToSet) throws DSException {
      // Remove already opened proof
      DbcProof proof = (DbcProof)proofEditPart.part().getAdapter(EObject.class);
      IDSProvable dsProvable = dsFinder.findProvable(proof.getTarget());
      if (dsProvable instanceof LoggingMethod) {
         ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
      }
      else if (dsProvable instanceof LoggingOperationContract) {
         ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
      }
      assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Set initial status
      Command setStatusCmd = SetCommand.create(domain, proof, DbcmodelPackage.Literals.DBC_PROOF__STATUS, statusToSet);
      domain.getCommandStack().execute(setStatusCmd);
      assertEquals(statusToSet, proof.getStatus());
      // Open proof
      TestInteractiveProvingUtil.openProof(startProofListener, editor, proofEditPart);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      if (allowProofResets) {
         assertEquals(DbcProofStatus.OPEN, proof.getStatus());
      }
      else {
         assertEquals(statusToSet, proof.getStatus());
      }
      assertTrue(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Open proof again (proof now opened, no reset required)
      setStatusCmd = SetCommand.create(domain, proof, DbcmodelPackage.Literals.DBC_PROOF__STATUS, statusToSet);
      domain.getCommandStack().execute(setStatusCmd);
      TestInteractiveProvingUtil.openProof(startProofListener, editor, proofEditPart);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      assertEquals(statusToSet, proof.getStatus());
      // Remove prove
      if (dsProvable instanceof LoggingMethod) {
         ((LoggingMethod)dsProvable).removeProof(proof.getObligation());
      }
      else if (dsProvable instanceof LoggingOperationContract) {
         ((LoggingOperationContract)dsProvable).removeProof(proof.getObligation());
      }
      assertFalse(dsProvable.hasInteractiveProof(proof.getObligation()));
      // Open proof again
      TestInteractiveProvingUtil.openProof(startProofListener, editor, proofEditPart);
      compareOpenProofCalls(model, "EnsuresPost", null, null);
      if (allowProofResets) {
         assertEquals(DbcProofStatus.OPEN, proof.getStatus());
      }
      else {
         assertEquals(statusToSet, proof.getStatus());
      }
      assertTrue(dsProvable.hasInteractiveProof(proof.getObligation()));
   }

   /**
    * Compares the proof references.
    * @param finder The {@link IDbcFinder} to use.
    * @param proof The proof to check.
    * @param expectedReferences The expected references.
    * @throws DSException Occurred Exception.
    */
   protected void compareProofReferences(IDbcFinder finder, 
                                         DbcProof proof, 
                                         List<IDSProvableReference> expectedReferences) throws DSException {
      assertNotNull(finder);
      assertNotNull(proof);
      assertNotNull(expectedReferences);
      assertEquals(expectedReferences.size(), proof.getProofReferences().size());
      Iterator<IDSProvableReference> expectedIter = expectedReferences.iterator();
      Iterator<DbcProofReference> currentIter = proof.getProofReferences().iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         IDSProvableReference expected = expectedIter.next();
         DbcProofReference current = currentIter.next();
         assertNotNull(expected);
         assertNotNull(current);
         assertEquals(expected.getLabel(), current.getKind());
         assertEquals(finder.findProvable(expected.getTargetProvable()), current.getTarget());
      }
      assertFalse(expectedIter.hasNext());
      assertFalse(currentIter.hasNext());
   }
   
   /**
    * Compares the proof references.
    * @param finder The {@link IDbcFinder} to use.
    * @param proofEditPart The proof edit part to check.
    * @param expectedReferences The expected references.
    * @throws DSException Occurred Exception.
    */
   protected void compareProofReferences(IDbcFinder finder, 
                                         SWTBotGefEditPart proofEditPart, 
                                         List<IDSProvableReference> expectedReferences) throws DSException {
      assertNotNull(proofEditPart);
      DbcProof proof = (DbcProof)TestInteractiveProvingUtil.getEditModel(proofEditPart);
      compareProofReferences(finder, proof, expectedReferences);
   }

   /**
    * Compares the status values on the given proofs.
    * @param c1EnsuresPost Given proof to check.
    * @param c0EnsuresPost Given proof to check.
    * @param incPreservesInv Given proof to check.
    * @param incInvalid Given proof to check.
    * @param noTarget Given proof to check.
    * @param c1RespectsModifies Expected status.
    * @param c1EnsuresPostStatus Expected status.
    * @param c0EnsuresPostStatus Expected status.
    * @param incPreservesInvStatus Expected status.
    * @param incInvalidStatus Expected status.
    * @param noTargetStatus Expected status.
    * @param c1RespectsModifiesStatus Expected status.
    */
   protected void compareProofStati(DbcProof c1EnsuresPost, 
                                    DbcProof c0EnsuresPost, 
                                    DbcProof incPreservesInv,
                                    DbcProof incInvalid, 
                                    DbcProof noTarget, 
                                    DbcProof c1RespectsModifies,
                                    DbcProofStatus c1EnsuresPostStatus,
                                    DbcProofStatus c0EnsuresPostStatus,
                                    DbcProofStatus incPreservesInvStatus,
                                    DbcProofStatus incInvalidStatus,
                                    DbcProofStatus noTargetStatus,
                                    DbcProofStatus c1RespectsModifiesStatus) {
      assertEquals(c1EnsuresPostStatus, c1EnsuresPost.getStatus());
      assertEquals(c0EnsuresPostStatus, c0EnsuresPost.getStatus());
      assertEquals(incPreservesInvStatus, incPreservesInv.getStatus());
      assertEquals(incInvalidStatus, incInvalid.getStatus());
      assertEquals(noTargetStatus, noTarget.getStatus());
      assertEquals(c1RespectsModifiesStatus, c1RespectsModifies.getStatus());
   }

   /**
    * Compares the status values on the given proofs.
    * @param c1EnsuresPost Given proof to check.
    * @param c0EnsuresPost Given proof to check.
    * @param incPreservesInv Given proof to check.
    * @param incInvalid Given proof to check.
    * @param noTarget Given proof to check.
    * @param c1RespectsModifies Expected status.
    * @param c1EnsuresPostStatus Expected status.
    * @param c0EnsuresPostStatus Expected status.
    * @param incPreservesInvStatus Expected status.
    * @param incInvalidStatus Expected status.
    * @param noTargetStatus Expected status.
    * @param c1RespectsModifiesStatus Expected status.
    */
   protected void compareProofStati(SWTBotGefEditPart c1EnsuresPost, 
                                    SWTBotGefEditPart c0EnsuresPost, 
                                    SWTBotGefEditPart incPreservesInv,
                                    SWTBotGefEditPart incInvalid, 
                                    SWTBotGefEditPart noTarget, 
                                    SWTBotGefEditPart c1RespectsModifies,
                                    DbcProofStatus c1EnsuresPostStatus,
                                    DbcProofStatus c0EnsuresPostStatus,
                                    DbcProofStatus incPreservesInvStatus,
                                    DbcProofStatus incInvalidStatus,
                                    DbcProofStatus noTargetStatus,
                                    DbcProofStatus c1RespectsModifiesStatus) {
      compareProofStati((DbcProof)TestInteractiveProvingUtil.getEditModel(c1EnsuresPost),
                        (DbcProof)TestInteractiveProvingUtil.getEditModel(c0EnsuresPost),
                        (DbcProof)TestInteractiveProvingUtil.getEditModel(incPreservesInv),
                        (DbcProof)TestInteractiveProvingUtil.getEditModel(incInvalid),
                        (DbcProof)TestInteractiveProvingUtil.getEditModel(noTarget),
                        (DbcProof)TestInteractiveProvingUtil.getEditModel(c1RespectsModifies),
                        c1EnsuresPostStatus,
                        c0EnsuresPostStatus,
                        incPreservesInvStatus,
                        incInvalidStatus,
                        noTargetStatus,
                        c1RespectsModifiesStatus);
   }
   
   /**
    * Compares the occurred method calls on the {@link IDSConnection} that
    * is used by the given model.
    * @param model The {@link DbcModel}. 
    * @param expectedC1 The expected obligation on c1 operation contract.
    * @param expectedC0 The expected obligation on c0 operation contract.
    * @param expectedInc The expected obligation on inc method.
    * @throws DSException Occurred Exception
    */
   protected void compareOpenProofCalls(DbcModel model, 
                                        String expectedC1, 
                                        String expectedC0,
                                        String expectedInc) throws DSException {
      // Make sure that the correct connection is established
      assertTrue(InteractiveConnectionUtil.isOpened(model));
      IDSConnection connection = InteractiveConnectionUtil.openConnection(model, null);
      assertTrue(connection.getDriver() instanceof SimpleProofModelDriver);
      assertTrue(connection.isConnected());
      assertTrue(connection.isInteractive());
      // Get data source model instances
      IDSClass mCDemo = connection.getClass("MCDemo");
      LoggingMethod inc = (LoggingMethod)mCDemo.getMethod("inc(x : int)");
      LoggingOperationContract c0 = (LoggingOperationContract)inc.getOperationContracts().get(0);
      LoggingMethod init = (LoggingMethod)mCDemo.getMethod("init(u : int)");
      LoggingOperationContract c1 = (LoggingOperationContract)init.getOperationContracts().get(0);
      // Make sure that the correct proof was opened
      if (expectedInc != null) {
         assertEquals(1, inc.getOpenInteractiveProofLog().size());
         assertEquals(expectedInc, inc.getOpenInteractiveProofLog().get(0));
      }
      else {
         assertEquals(0, inc.getOpenInteractiveProofLog().size());
      }
      if (expectedC0 != null) {
         assertEquals(1, c0.getOpenInteractiveProofLog().size());
         assertEquals(expectedC0, c0.getOpenInteractiveProofLog().get(0));
      }
      else {
         assertEquals(0, c0.getOpenInteractiveProofLog().size());
      }
      assertEquals(0, init.getOpenInteractiveProofLog().size());
      if (expectedC1 != null) {
         assertEquals(1, c1.getOpenInteractiveProofLog().size());
         assertEquals(expectedC1, c1.getOpenInteractiveProofLog().get(0));
      }
      else {
         assertEquals(0, c1.getOpenInteractiveProofLog().size());
      }
      // Clear calls
      inc.getOpenInteractiveProofLog().clear();
      c0.getOpenInteractiveProofLog().clear();
      init.getOpenInteractiveProofLog().clear();
      c1.getOpenInteractiveProofLog().clear();
   }
}