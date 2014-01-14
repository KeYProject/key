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

package org.key_project.keyide.ui.test.testcase.swtbot;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.junit.Test;
import org.key_project.key4eclipse.test.util.TestKeY4EclipseUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.util.MiscTools;

public class SWTBotManualRuleApplicationTest extends AbstractSWTBotKeYEditorTest {
   @Test
   public void testCloseFalse_ProofClosed() throws Exception {
      doStartProofTest("SWTBotManualRuleApplicationTest_testCloseFalse_ProofClosed", 
                       new IStopCondition() {
                          @Override
                          public boolean shouldStop(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
                              return false;
                          }
                        
                          @Override
                          public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
                             RuleApp ruleApp = goal.getRuleAppManager().peekNext();
                             return !"closeFalse".equals(MiscTools.getRuleName(ruleApp)) ||
                                    proof.openEnabledGoals().size() >= 2; // Stop before last goal is closed with closeFalse
                          }
                        
                          @Override
                          public String getStopMessage(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
                              return null;
                          }
                        
                          @Override
                          public int getMaximalWork(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser) {
                              return 0;
                          }
                        
                          @Override
                          public String getGoalNotAllowedMessage(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
                             return null;
                          }
                       },
                       25, // x of false in text control of editor
                       7, // y of false in text control of editor
                       "closeFalse",
                       true);
   }
   
   @Test
   public void testAssignment_ProofStillOpen() throws Exception {
      doStartProofTest("SWTBotManualRuleApplicationTest_testAssignment_ProofStillOpen", 
                       null,
                       110, // x of assignment text control of editor
                       180, // y of assignment text control of editor
                       "assignment",
                       false);
   }
   
   protected void doStartProofTest(String projectName, 
                                   final IStopCondition stopCondition,
                                   final int x,
                                   final int y,
                                   final String ruleNameToApply,
                                   final boolean expectedProofClosed) throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, 
                          KeYEnvironment<CustomConsoleUserInterface> environment, 
                          Proof proof, 
                          SWTWorkbenchBot bot, 
                          SWTBotEditor editor, 
                          KeYEditor keyEditor) throws Exception {
            assertFalse(keyEditor.getCurrentProof().closed());
            // Make sure that start stop auto mode buttons are as expected
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            // Start auto mode if required
            if (stopCondition != null) {
               StrategySettings ss = keyEditor.getCurrentProof().getSettings().getStrategySettings();
               ss.setCustomApplyStrategyStopCondition(stopCondition);
               keyEditor.getUI().startAndWaitForAutoMode(keyEditor.getCurrentProof());
            }
            // Get node to apply rule on
            Node node = keyEditor.getCurrentNode();
            assertFalse(node.isClosed());
            assertEquals(0, node.childrenCount());
            // Apply rule "assignment" interactively
            final SWTBotStyledText styledText = editor.bot().styledText();
            TestUtilsUtil.setCursorLocation(styledText, x, y);
            TestUtilsUtil.clickContextMenu(styledText, x, y, ruleNameToApply);
            // Make sure that correct rule was applied
            assertEquals(expectedProofClosed, keyEditor.getCurrentProof().closed());
            assertEquals(1, node.childrenCount());
            assertEquals(ruleNameToApply, MiscTools.getRuleDisplayName(node));
            assertEquals(expectedProofClosed, node.isClosed());
            // Make sure that start stop auto mode buttons are as expected
            assertEquals(!expectedProofClosed, bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         }
      };
      doEditorTest(projectName, 
                   "data/paycard", 
                   TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "isValid()", "0", "normal_behavior"),
                   5,
                   false, 
                   steps);
   }
}