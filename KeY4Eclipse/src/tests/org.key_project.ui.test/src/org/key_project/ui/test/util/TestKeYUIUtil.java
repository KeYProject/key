/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

package org.key_project.ui.test.util;

import static org.junit.Assert.assertNotNull;

import javax.swing.tree.TreeModel;
import javax.swing.tree.TreeNode;

import junit.framework.TestCase;

import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.key_project.swtbot.swing.bot.AbstractSwingBotComponent;
import org.key_project.swtbot.swing.bot.SwingBot;
import org.key_project.swtbot.swing.bot.SwingBotJButton;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;
import org.key_project.swtbot.swing.bot.SwingBotJRadioButton;
import org.key_project.swtbot.swing.bot.SwingBotJTabbedPane;
import org.key_project.swtbot.swing.bot.SwingBotJTree;
import org.key_project.swtbot.swing.bot.finder.waits.Conditions;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.TestUtilsUtil.MethodTreatment;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.EnvNode;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.TaskTreeModel;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * Provides static methods that makes testing easier.
 * @author Martin Hentschel
 */
public final class TestKeYUIUtil {
   /**
    * Forbid instances.
    */
   private TestKeYUIUtil() {
   }
   
   /**
    * Creates an operation contract ID.
    * @param qualifiedName The qualified class name.
    * @param methodClassQualifiedName The name of the class which contains the method implementation.
    * @param method The method signature.
    * @param id The unique ID.
    * @param behavior The behavior.
    * @return The created operation contract ID:
    */
   public static String createOperationContractId(String qualifiedName,
                                                  String methodClassQualifiedName,
                                                  String method,
                                                  String id,
                                                  String behavior) {
      return qualifiedName + "[" + methodClassQualifiedName + "::" + method + "].JML " + (StringUtil.isEmpty(behavior) ? "" : behavior + " ") + "operation contract." + id + "";
   }

   /**
    * Creates the ID for an axiom contract.
    * @param qualifiedName The full qualified class name.
    * @param field The field.
    * @param id The unique ID.
    * @return the create axiom contract ID.
    */
   public static String createAxiomContractId(String qualifiedName, String field, String id) {
      return createCompleteAxiomContractId(qualifiedName, qualifiedName + "::" + field, id);
   }

   /**
    * Creates the ID for an axiom contract.
    * @param qualifiedName The full qualified class name.
    * @param field The field.
    * @param id The unique ID.
    * @return the create axiom contract ID.
    */
   public static String createCompleteAxiomContractId(String qualifiedName, String field, String id) {
      return qualifiedName + "[" + field + "].JML accessible clause." + id;
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
       SwingBotJFrame frame = keyGetMainWindow();
       frame.close();
       TestCase.assertFalse(frame.isOpen());
   }
   
   /**
    * Makes sure that the correct proofs are shown in the proof tree.
    * @param selectedProof The expected selected proof.
    * @param availableProofs The expected available proofs.
    */
   public static void keyCheckProofs(String selectedProof, String... availableProofs) {
       SwingBotJFrame frame = keyGetMainWindow();
       SwingBotJTree tree = frame.bot().jTree(TaskTreeModel.class);
       keyCheckAvailableProofs(tree, availableProofs);
       keyCheckSelectedProof(tree, selectedProof);
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
    * Starts the selected proof in the opened {@link ProofManagementDialog}.
    */
   public static void keyStartSelectedProofInProofManagementDiaolog() {
       SwingBotJFrame frame = keyGetMainWindow();
       SwingBotJDialog dialog = keyGetProofManagementDiaolog(frame);
       TestCase.assertTrue(dialog.isOpen());
       SwingBotJButton startButton = dialog.bot().jButton("Start Proof");
       startButton.clickAndWait();
       TestCase.assertFalse(dialog.isOpen());
   }
   
   /**
    * Sets the method treatment in KeY's main window.
    * @param methodTreatment The method treatment to use.
    */
   public static void keySetMethodTreatment(MethodTreatment methodTreatment) {
      keySetMethodTreatment(keyGetMainWindow(), methodTreatment);
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
    * Executes the "Start/stop automated proof search" on the given KeY frame.
    * @param frame The given KeY frame.
    * @param methodTreatment The method treatment to use.
    */
   public static void keyFinishSelectedProofAutomatically(SwingBotJFrame frame, MethodTreatment methodTreatment) {
      keySetMethodTreatment(frame, methodTreatment);
      // Run proof completion
      frame.bot().jTree().unselectAll();
      frame.bot().waitWhile(Conditions.hasSelection(frame.bot().jTree()));
      SwingBotJButton button = frame.bot().jButtonWithTooltip("Start/stop automated proof search");
      button.click();
      frame.bot().waitUntil(Conditions.hasSelection(frame.bot().jTree()));
      // Close result dialog
      SwingBotJDialog proofClosedDialog = frame.bot().jDialog("Proof closed");
      proofClosedDialog.bot().jButton("OK").click();
      proofClosedDialog.bot().waitUntil(Conditions.componentCloses(proofClosedDialog));
      TestCase.assertFalse(proofClosedDialog.isOpen());   
   }
   
   /**
    * Sets the method treatment in KeY.
    * @param frame The given KeY frame.
    * @param methodTreatment The method treatment to use.
    */
   public static void keySetMethodTreatment(SwingBotJFrame frame, MethodTreatment methodTreatment) {
      // Set proof search strategy settings
      SwingBotJTabbedPane pane = frame.bot().jTabbedPane();
      TestCase.assertEquals("Proof Search Strategy", pane.getTitleAt(2));
      AbstractSwingBotComponent<?> tabComponent = pane.select(2);
      if (MethodTreatment.CONTRACTS.equals(methodTreatment)) {
         SwingBotJRadioButton contractsButton = tabComponent.bot().jRadioButton("Contract", 1);
         contractsButton.click();
      }
      else {
         SwingBotJRadioButton expandButton = tabComponent.bot().jRadioButton("Expand", 2);
         expandButton.click();
      }
      TestCase.assertEquals("Proof", pane.getTitleAt(0));
      pane.select(0);
   }
   
   /**
    * Searches a {@link IProgramMethod} in the given {@link Services}.
    * @param services The {@link Services} to search in.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @return The first found {@link IProgramMethod} in the type.
    */
   public static IProgramMethod searchProgramMethod(Services services, 
                                                    String containerTypeName, 
                                                    final String methodFullName) {
      JavaInfo javaInfo = services.getJavaInfo();
      KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
      assertNotNull(containerKJT);
      ImmutableList<IProgramMethod> pms = javaInfo.getAllProgramMethods(containerKJT);
      IProgramMethod pm = CollectionUtil.search(pms, new IFilter<IProgramMethod>() {
         @Override
         public boolean select(IProgramMethod element) {
            return methodFullName.equals(element.getFullName());
         }
      });
      assertNotNull(pm);
      return pm;
   }

   /**
    * Blocks the current thread until the auto mode has started.
    * @param ui The {@link UserInterfaceControl} to wait for its auto mode.
    */
   public static void waitUntilAutoMode(SWTBot bot, final UserInterfaceControl ui) {
      bot.waitUntil(new ICondition() {
         @Override
         public boolean test() throws Exception {
            return ui.getProofControl().isInAutoMode();
         }
         
         @Override
         public void init(SWTBot bot) {
         }
         
         @Override
         public String getFailureMessage() {
            return "UserInterfaceControl \"" + ui + "\" is not in automode.";
         }
      });
   }

   /**
    * Blocks the current thread while the auto mode is running.
    * @param ui The {@link UserInterfaceControl} to wait for its auto mode.
    */
   public static void waitWhileAutoMode(SWTBot bot, final UserInterfaceControl ui) {
      bot.waitUntil(new ICondition() {
         @Override
         public boolean test() throws Exception {
            return !ui.getProofControl().isInAutoMode();
         }
         
         @Override
         public void init(SWTBot bot) {
         }
         
         @Override
         public String getFailureMessage() {
            return "UserInterfaceControl \"" + ui + "\" is still in automode.";
         }
      });
   }
   
   /**
    * Goes to the selected proof in the opened {@link ProofManagementDialog}.
    */
   public static void keyGoToSelectedProofInProofManagementDiaolog() {
       SwingBotJFrame frame = keyGetMainWindow();
       SwingBotJDialog dialog = keyGetProofManagementDiaolog(frame);
       TestCase.assertTrue(dialog.isOpen());
       SwingBotJButton goToButton = dialog.bot().jButton("Go to Proof");
       goToButton.clickAndWait();
       TestCase.assertFalse(dialog.isOpen());
   }

   /**
    * Returns the {@link Proof} in the proof list at
    * the given index.
    * @param envIndex The index of the {@link ProofEnvironment}.
    * @param proofIndex The index of the {@link Proof} in the {@link ProofEnvironment}.
    * @return The found {@link ProofEnvironment}.
    */
   public static Proof keyGetProof(int envIndex, int proofIndex) {
       SwingBotJFrame frame = keyGetMainWindow();
       SwingBotJTree tree = frame.bot().jTree(TaskTreeModel.class);
       return keyGetProof(tree, envIndex, proofIndex);
   }
   
   /**
    * Returns the {@link ProofEnvironment} in the proof list at
    * the given index.
    * @param tree The {@link SwingBotJTree} to search in.
    * @param envIndex The index of the {@link ProofEnvironment}.
    * @param proofIndex The index of the {@link Proof} in the {@link ProofEnvironment}.
    * @return The found {@link ProofEnvironment}.
    */
   public static Proof keyGetProof(SwingBotJTree tree, int envIndex, int proofIndex) {
       TestCase.assertNotNull(tree);
       TestCase.assertTrue(envIndex >= 0);
       TestCase.assertTrue(proofIndex >= 0);
       TreeModel model = tree.getModel();
       TestCase.assertNotNull(model);
       TestCase.assertTrue(envIndex < model.getChildCount(model.getRoot()));
       Object child = model.getChild(model.getRoot(), envIndex);
       TestCase.assertTrue(child instanceof EnvNode);
       TreeNode proofNode = ((EnvNode)child).getChildAt(proofIndex);
       TestCase.assertTrue(child instanceof TaskTreeNode);
       return ((TaskTreeNode)proofNode).proof();
   }
}