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

package org.key_project.sed.key.ui.test.testcase.swtbot;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.starter.KeYIDEProofStarter;
import org.key_project.keyide.ui.util.KeYIDEPreferences;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.testcase.swtbot.AbstractKeYDebugTargetTestCase;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Tests the open proof functionality.
 * @author Martin Hentschel
 */
public class SWTBotOpenProofTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests to open a proof.
    */
   @Test
   public void testOpenProof() throws Exception {
      boolean originalDoNotAsk = StarterPreferenceUtil.isDontAskForProofStarter();
      String originalProofStarter = StarterPreferenceUtil.getSelectedProofStarterID();
      String originalSwitch = KeYIDEPreferences.getSwitchToKeyPerspective();
      StarterPreferenceUtil.setDontAskForProofStarter(true);
      StarterPreferenceUtil.setSelectedProofStarterID(KeYIDEProofStarter.STARTER_ID);
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.NEVER);
      try {
         IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
            @Override
            public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
               // Resume on thread
               SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
               stepInto(bot, item, target);
               // Open editor
               TestUtilsUtil.clickContextMenu(debugTree, "Open Proof");
               SWTBotEditor editor = bot.activeEditor();
               KeYEditor keyEditor = (KeYEditor)editor.getReference().getEditor(true);
               assertTrue(target instanceof KeYDebugTarget);
               assertSame(((KeYDebugTarget)target).getProof(), keyEditor.getCurrentProof());
               // Close editor
               editor.close();
               assertFalse(((KeYDebugTarget)target).getProof().isDisposed());
               stepInto(bot, item, target);
            }
         };
         doKeYDebugTargetTest("SWTBotOpenProofTest_testOpenProof", 
                              Activator.PLUGIN_ID,
                              "data/statements", 
                              false,
                              false, 
                              createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"), 
                              null,
                              null,
                              Boolean.FALSE, 
                              Boolean.FALSE, 
                              Boolean.FALSE, 
                              Boolean.FALSE,
                              Boolean.FALSE,
                              8, 
                              executor);
      }
      finally {
         StarterPreferenceUtil.setDontAskForProofStarter(originalDoNotAsk);
         StarterPreferenceUtil.setSelectedProofStarterID(originalProofStarter);
         KeYIDEPreferences.setSwitchToKeyPerspective(originalSwitch);
      }
   }
   
   /**
    * Makes sure that no proof can be opened in case of shown {@link MainWindow}.
    */
   @Test
   public void testOpenProof_KeYMainWindow() throws Exception {
      boolean originalDoNotAsk = StarterPreferenceUtil.isDontAskForProofStarter();
      String originalProofStarter = StarterPreferenceUtil.getSelectedProofStarterID();
      String originalSwitch = KeYIDEPreferences.getSwitchToKeyPerspective();
      StarterPreferenceUtil.setDontAskForProofStarter(true);
      StarterPreferenceUtil.setSelectedProofStarterID(KeYIDEProofStarter.STARTER_ID);
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.NEVER);
      try {
         IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
            @Override
            public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
               // Resume on thread
               SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
               stepInto(bot, item, target);
               // Make sure that open proof is not available
               try {
                  TestUtilsUtil.clickContextMenu(debugTree, "Open Proof"); // Behavior in Eclipse 3.x is to throw an Exception because not available, in Eclipse 4.x the item is disabled and no Exception is thrown. 
                  assertFalse(debugTree.contextMenu("Open Proof").isEnabled()); // Behavior in Eclipse 4.x
               }
               catch (WidgetNotFoundException e) {
                  // Not visible (behavior in Eclipse 3.x)
               }
            }
         };
         doKeYDebugTargetTest("SWTBotOpenProofTest_testOpenProof_KeYMainWindow", 
                              Activator.PLUGIN_ID,
                              "data/statements", 
                              false,
                              false, 
                              createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"), 
                              null,
                              null,
                              Boolean.FALSE, 
                              Boolean.FALSE, 
                              Boolean.TRUE, 
                              Boolean.FALSE,
                              Boolean.FALSE,
                              8, 
                              executor);
      }
      finally {
         StarterPreferenceUtil.setDontAskForProofStarter(originalDoNotAsk);
         StarterPreferenceUtil.setSelectedProofStarterID(originalProofStarter);
         KeYIDEPreferences.setSwitchToKeyPerspective(originalSwitch);
      }
   }
}