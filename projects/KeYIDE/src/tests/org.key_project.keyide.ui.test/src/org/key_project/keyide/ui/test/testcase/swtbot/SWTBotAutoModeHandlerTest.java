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
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.junit.Test;
import org.key_project.key4eclipse.test.util.SuspendingStopCondition;
import org.key_project.key4eclipse.test.util.TestKeY4EclipseUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.handlers.StartAutoModeHandler;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * <p>
 * SWTBot tests for {@link StartAutoModeHandler}.
 * </p>
 * <p>
 * Requires the following JVM settings: -Xms128m -Xmx1024m -XX:MaxPermSize=256m
 * </p>
 * <p>
 * If you got timeout exceptions increase the waiting time with the following
 * additional JVM parameter: -Dorg.eclipse.swtbot.search.timeout=10000
 * </p>
 * @author Niklas Bunzel
 */
public class SWTBotAutoModeHandlerTest extends AbstractSWTBotKeYEditorTest {
   /**
    * Tests starting the auto mode. Proof is still open after the auto mode.
    */
   @Test
   public void testStartAutoMode_proofOpen() throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, 
                          KeYEnvironment<CustomUserInterface> environment, 
                          Proof proof, 
                          SWTWorkbenchBot bot, 
                          SWTBotEditor editor, 
                          KeYEditor keyEditor) throws Exception {
            assertNotNull(keyEditor.getCurrentProof());
            assertFalse(keyEditor.getCurrentProof().closed());
            SuspendingStopCondition sleepCondition = new SuspendingStopCondition();
            sleepCondition.setMaxRules(100);
            keyEditor.getCurrentProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(sleepCondition);
            
            //check that the auto mode is available
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is disabled
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            //start auto mode
            sleepCondition.setSleep(true);
            TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
            TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getUI());
            //check that auto mode is not available while auto mode is running
            assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is enabled
            assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            sleepCondition.setSleep(false);
            // Make sure that the proof is not closed
            TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getUI());
            assertFalse(keyEditor.getCurrentProof().closed());
            // Make sure that start is enabled and stop is disabled
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled()); 
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         }
      };
      doEditorTest("SWTBotStartAutoModeHandlerTest_testStartAutoMode_proofOpen", 
                   "data/paycard", 
                   true, 
                   TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "chargeAndRecord(int)", "0", "normal_behavior"),
                   5,
                   false, 
                   steps);
   }
   
   /**
    * Tests starting the auto mode. Proof is closed after the auto mode.
    */
   @Test
   public void testStartAutoMode_proofClosed() throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, 
                          KeYEnvironment<CustomUserInterface> environment, 
                          Proof proof, 
                          SWTWorkbenchBot bot, 
                          SWTBotEditor editor, 
                          KeYEditor keyEditor) throws Exception {
            assertNotNull(keyEditor.getCurrentProof());
            assertFalse(keyEditor.getCurrentProof().closed());
            SuspendingStopCondition sleepCondition = new SuspendingStopCondition();
            keyEditor.getCurrentProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(sleepCondition);
            
            //check that the auto mode is available
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is disabled
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            //start auto mode
            sleepCondition.setSleep(true);
            TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
            TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getUI());
            //check that auto mode is not available while auto mode is running
            assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is enabled
            assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            // Make sure that the proof is closed
            sleepCondition.setSleep(false);
            TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getUI());
            assertTrue(keyEditor.getCurrentProof().closed());
            // Make sure that start/stop are both disabled
            assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled()); 
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         }
      };
      doEditorTest("SWTBotStartAutoModeHandlerTest_testStartAutoMode", 
                   "data/paycard", 
                   true, 
                   TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "isValid()", "0", "normal_behavior"),
                   5,
                   false, 
                   steps);
   }
   
   /**
    * Test starts the automode, stops the automode and restarts it till the proof is closed.
    */
   @Test
   public void testStopAutoMode_RestartAutoMode_ProofClosed() throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, 
                          KeYEnvironment<CustomUserInterface> environment, 
                          Proof proof, 
                          SWTWorkbenchBot bot, 
                          SWTBotEditor editor, 
                          KeYEditor keyEditor) throws Exception {
            SuspendingStopCondition sleepCondition = new SuspendingStopCondition();
            keyEditor.getCurrentProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(sleepCondition);
            //check that the auto mode is available
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is disabled
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            //start auto mode
            sleepCondition.setMaxRules(10);
            sleepCondition.setSleep(true);
            TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
            TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getUI());
            //check that auto mode is not available while auto mode is running
            assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is enabled
            assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
                 
            //stop auto mode and wait until it has stopped
            TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Stop Auto Mode"));
            sleepCondition.setSleep(false);
            TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getUI());
            //check that auto mode is available again
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is disabled
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            // Make sure that the proof is still open (not closed)
            assertFalse(keyEditor.getCurrentProof().closed());
            //restart auto mode
            sleepCondition.setMaxRules(Integer.MAX_VALUE);
            sleepCondition.setSleep(true);
            TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
            TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getUI());
            //check that auto mode is not available while auto mode is running
            assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is enabled
            assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            sleepCondition.setSleep(false);
            TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getUI());
            //make sure proof is closed
            assertTrue(keyEditor.getCurrentProof().closed());
            //check that the start and stop buttons are both disabled
            assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         }
      };
      doEditorTest("SWTBotStopAutoModeHandlerTest_testStopAutoMode_RestartAutoMode_ProofClosed", 
                   "data/paycard", 
                   true, 
                   TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "charge(int)", "0", "normal_behavior"),
                   5,
                   false, 
                   steps);
   }

   /**
    * Test starts and stops the automode. The proof is still open after automode stopped.
    */
   @Test
   public void testStopAutoMode_ProofOpen() throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, 
                          KeYEnvironment<CustomUserInterface> environment, 
                          Proof proof, 
                          SWTWorkbenchBot bot, 
                          SWTBotEditor editor, 
                          KeYEditor keyEditor) throws Exception {
            SuspendingStopCondition sleepCondition = new SuspendingStopCondition();
            keyEditor.getCurrentProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(sleepCondition);
            //check that the auto mode is available
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is disabled
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            //start auto mode
            sleepCondition.setSleep(true);
            TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
            TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getUI());
            //check that auto mode is not available while auto mode is running
            assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is enabled
            assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
                     
            //stop auto mode and wait until it has stopped
            TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Stop Auto Mode"));
            sleepCondition.setSleep(false);
            TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getUI());
            //make sure proof is still open
            assertFalse(keyEditor.getCurrentProof().closed());
            //check that auto mode is available again
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //stop auto mode is disabled
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         }
      };
      doEditorTest("SWTBotStopAutoModeHandlerTest_testStopAutoMode_ProofOpen", 
                   "data/paycard", 
                   true, 
                   TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "chargeAndRecord(int)", "0", "normal_behavior"),
                   5,
                   false, 
                   steps);
   }
}