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

package org.key_project.keyide.ui.test.testcase.swtbot;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
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
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomUserInterface;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Tests the interactive rule application in the {@link KeYEditor}.
 * @author Martin Hentschel
 */
public class SWTBotManualRuleApplicationTest extends AbstractSWTBotKeYEditorTest {
   /**
    * Tests the application of a closing rule which closes the full proof.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testCloseFalse_ProofClosed() throws Exception {
      doStartProofTest("SWTBotManualRuleApplicationTest_testCloseFalse_ProofClosed", 
                       "data/paycard",
                       TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "isValid()", "0", "normal_behavior"),
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
                       true,
                       "false",
                       "closeFalse",
                       null,
                       1,
                       true);
   }
   
   /**
    * Tests the application of the assignment rule which leafs the proof still open.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testAssignment_ProofStillOpen() throws Exception {
      doStartProofTest("SWTBotManualRuleApplicationTest_testAssignment_ProofStillOpen", 
                       "data/paycard",
                       TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "isValid()", "0", "normal_behavior"),
                       null,
                       false,
                       "exc=null;",
                       "assignment",
                       null,
                       1,
                       false);
   }
   
   @Test
   public void testUseOperationContract_Cancel() throws Exception {
      IAppliedRuleTest appliedRuleTest =  new IAppliedRuleTest() {
         @Override
         public void test(IJavaProject project, KeYEnvironment<CustomUserInterface> environment, Proof proof, SWTWorkbenchBot bot, SWTBotEditor editor, KeYEditor keyEditor, Node nodeOnWhichRuleIsApplied) {
            SWTBotShell shell = bot.shell("Contracts for charge");
            TestUtilsUtil.clickDirectly(shell.bot().button("Cancel"));
         }
      };
      doStartProofTest("SWTBotManualRuleApplicationTest_testUseOperationContract_Cancel",
                        "data/paycard",
                        TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "chargeAndRecord(int)", "0", "normal_behavior"),
                        new IStopCondition() {
                           @Override
                           public boolean shouldStop(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
                              return false;
                           }
                           
                           @Override
                           public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
                              RuleApp ruleApp = goal.getRuleAppManager().peekNext();
                              return !"Use Operation Contract".equals(MiscTools.getRuleName(ruleApp));
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
                        true,
                        "exc:=null}",
                        "Use Operation Contract",
                        appliedRuleTest,
                        0,
                        false);
   }
   
   /**
    * Performs the following test steps to test an interactive rule application:
    * <ol>
    *    <li>New project is created in workspace.</li>
    *    <li>Source code to test is extracted from plug-in into the created project.</li>
    *    <li>A proof is instantiated and opened in the {@link KeYEditor}.</li>
    *    <li>The auto mode is started to reach a proof {@link Node} where the rule to test can be applied at.</li>
    *    <li>The rule to test is applied interactively.</li>
    *    <li>Arbitrary test steps implemented as {@link IAppliedRuleTest} are optionally executed.</li>
    *    <li>The proof closed state is ensured.</li>
     * </ol>
    * @param projectName The unique project name of the project which will be created in the workspace.
    * @param pathToSourceCodeInTestPlugin The path to the source code in the test plug-in which will be extracted into the created project.
    * @param contractId The unique ID of the proof obligation (contract) for which a proof will be started.
    * @param stopCondition An optional custom {@link IStopCondition} which stops the started auto mode at a node on which the rule to test can be applied.
    * @param useOperationContracts {@code true} use operation contracts, {@code false} inline methods instead
    * @param textToApplyRuleOn The text in the {@link KeYEditor} for which the context menu contains the rule to apply.
    * @param ruleNameToApply The name of the rule to apply.
    * @param appliedRuleTest Optionally, some additional test steps, e.g. to deal with an opened {@link Shell}.
    * @param expectedNumOfChildrenAfterRuleApplication The number of child branches the rule creates or {@code 0} if no rule is applied.
    * @param expectedProofClosed {@code true} {@link Proof} should be closed after rule application, {@code false} {@link Proof} will be still open.
    * @throws Exception Occurred Exception.
    */
   protected void doStartProofTest(String projectName,
                                   String pathToSourceCodeInTestPlugin,
                                   String contractId,
                                   final IStopCondition stopCondition,
                                   final boolean useOperationContracts,
                                   final String textToApplyRuleOn,
                                   final String ruleNameToApply,
                                   final IAppliedRuleTest appliedRuleTest,
                                   final int expectedNumOfChildrenAfterRuleApplication,
                                   final boolean expectedProofClosed) throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, 
                          KeYEnvironment<CustomUserInterface> environment, 
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
               SymbolicExecutionUtil.updateStrategySettings(proof, useOperationContracts, true, false, false);
               StrategyProperties p = ss.getActiveStrategyProperties();
               p.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, useOperationContracts ? StrategyProperties.METHOD_CONTRACT : StrategyProperties.METHOD_EXPAND);
               ss.setActiveStrategyProperties(p);
               keyEditor.getUI().startAndWaitForAutoMode(keyEditor.getCurrentProof());
            }
            // Get node to apply rule on
            Node node = keyEditor.getCurrentNode();
            assertFalse(node.isClosed());
            assertEquals(0, node.childrenCount());
            // Apply rule interactively
            final SWTBotStyledText styledText = editor.bot().styledText();
            Point point = TestUtilsUtil.selectText(styledText, textToApplyRuleOn);
            TestUtilsUtil.setCursorLocation(styledText, point.x - 5, point.y);
            TestUtilsUtil.clickContextMenu(styledText, point.x - 5, point.y, ruleNameToApply);
            if (appliedRuleTest != null) {
               appliedRuleTest.test(project, environment, proof, bot, editor, keyEditor, node);
            }
            // Make sure that correct rule was applied
            assertEquals(expectedProofClosed, keyEditor.getCurrentProof().closed());
            assertEquals(expectedNumOfChildrenAfterRuleApplication, node.childrenCount());
            if (expectedNumOfChildrenAfterRuleApplication >= 1) {
               assertEquals(ruleNameToApply, MiscTools.getRuleDisplayName(node));
            }
            assertEquals(expectedProofClosed, node.isClosed());
            // Make sure that start stop auto mode buttons are as expected
            assertEquals(!expectedProofClosed, bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         }
      };
      doEditorTest(projectName, 
                   pathToSourceCodeInTestPlugin, 
                   contractId,
                   5,
                   false, 
                   steps); 
   }
   
   /**
    * Some additional test steps used by {@link SWTBotManualRuleApplicationTest#doStartProofTest(String, IStopCondition, int, int, String, IAppliedRuleTest, boolean)} to finish and test an applied rule.
    * @author Martin Hentschel
    */
   protected static interface IAppliedRuleTest {
      /**
       * Finishes and tests a rule application.
       * @param project The {@link IJavaProject} which contains the source code.
       * @param environment The loaded {@link KeYEnvironment}.
       * @param proof The current {@link Proof}.
       * @param bot The {@link SWTWorkbenchBot} to use.
       * @param editor The SWTBot editor in which the {@link Proof} is shown.
       * @param keyEditor The {@link KeYEditor} in which the {@link Proof} is shown.
       * @param nodeOnWhichRuleIsApplied The {@link Node} on which the rule is applied.
       */
      public void test(IJavaProject project, 
                       KeYEnvironment<CustomUserInterface> environment, 
                       Proof proof, 
                       SWTWorkbenchBot bot, 
                       SWTBotEditor editor, 
                       KeYEditor keyEditor,
                       Node nodeOnWhichRuleIsApplied);
   }
}