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
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotWorkbenchPart;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.ui.IEditorReference;
import org.junit.Test;
import org.key_project.core.test.util.SuspendingStopCondition;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.handlers.StartAutoModeHandler;
import org.key_project.ui.test.util.TestKeYUIUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;

/**
 * <p>
 * SWTBot tests for {@link MinimizeInteractionsHandler}.
 * </p>
 * <p>
 * Requires the following JVM settings: -Xms128m -Xmx1024m -XX:MaxPermSize=256m
 * </p>
 * <p>
 * If you got timeout exceptions increase the waiting time with the following
 * additional JVM parameter: -Dorg.eclipse.swtbot.search.timeout=10000
 * </p>
 * @author Viktor Pfanschilling
 */
public class SWTBotMinimizeInteractionsHandlerTest extends AbstractSWTBotKeYEditorTest {
   /**
    * Tests starting the auto mode. Proof is still open after the auto mode.
    */
   @Test
   public void testStartAutoMode_proofOpen() throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, 
                          KeYEnvironment<DefaultUserInterfaceControl> environment, 
                          Proof proof, 
                          SWTWorkbenchBot bot, 
                          SWTBotEditor editor, 
                          KeYEditor keyEditor) throws Exception {
            assertNotNull(keyEditor.getCurrentProof());
            
            String rule = "replace_known_right";
            //test whether we see the rule right now:
            // right click 3 places to the left of the first '&' and check for the rule
            boolean exists_pre = openRuleDialog(bot, editor, "&", rule, -3);
            
            //toggle
            TestUtilsUtil.clickDirectly(bot.toolbarToggleButtonWithTooltip("Minimize Interactions"));
            
            //check again. the rule specified above depends on un-minimized interactions.
            boolean exists_post = openRuleDialog(bot, editor, "&", rule, -3);
            
            //consequently, since we toggled that, we should have seen it exactly once:
            assertFalse(exists_pre == exists_post);
            
            //restore original state.
            TestUtilsUtil.clickDirectly(bot.toolbarToggleButtonWithTooltip("Minimize Interactions"));
         }
      };
      doEditorTest("SWTBotStartAutoModeHandlerTest_testStartAutoMode_proofOpen", 
                   "data/paycard", 
                   true, 
                   TestKeYUIUtil.createOperationContractId("PayCard", "PayCard", "chargeAndRecord(int)", "0", "normal_behavior"),
                   5,
                   false, 
                   steps);
   }
   
   /**
    * determines whether a rule is applicable on the given text.
    * @param location The text snippet where to look for the rule
    * @param rule The name of the rule to be applied
    * @param offset The offset in chars where to look relative to location
    * @param editor 
    */
   private boolean openRuleDialog(SWTWorkbenchBot bot, SWTBotEditor editor, String location, String rule, int offset) {
      //click context menu / text we're looking for.
      final SWTBotStyledText styledText = editor.bot().styledText();
      Point point = TestUtilsUtil.selectText(styledText, location);
      point.x = point.x - 1 + offset;
      
      TestUtilsUtil.setCursorLocation(styledText, point.x, point.y);
      
      //Try to apply the specified rule, return null if not found. 
      //If not found, this should not timeout like SWT would.
      try {
         TestUtilsUtil.clickContextMenu(styledText, point.x, point.y, rule);
      } catch(Exception e) {
         return false;
      }
      //cancel the rule application dialog.
      SWTBotShell shell = bot.activeShell();
      shell.bot().button("Cancel").click();
      return true;
   }
}