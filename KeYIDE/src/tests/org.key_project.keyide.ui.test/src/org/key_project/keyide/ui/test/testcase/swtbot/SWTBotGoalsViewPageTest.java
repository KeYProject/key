package org.key_project.keyide.ui.test.testcase.swtbot;

import java.util.Iterator;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.utils.TableCollection;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.core.test.util.SuspendingStopCondition;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.views.GoalsView;
import org.key_project.ui.test.util.TestKeYUIUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * SWTBot tests for {@GoalsView} and {@GoalsPage}.
 * @author Seena Vellaramkalayil
 */
public class SWTBotGoalsViewPageTest extends AbstractSWTBotKeYEditorTest {
   /**
    * tests if the list of goals is shown right before the auto mode
    *  and after the auto mode.
    * @throws Exception
    */
   @Test
   public void testGoalsView_beforeAndAfterAutoMode() throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, KeYEnvironment<DefaultUserInterfaceControl> environment, Proof proof, SWTWorkbenchBot bot, SWTBotEditor editor, KeYEditor keyEditor) throws Exception {
            assertNotNull(keyEditor.getCurrentProof());
            assertFalse(keyEditor.getCurrentProof().closed());
            //open GoalsView
            TestUtilsUtil.openView(GoalsView.VIEW_ID);
            SWTBotView goalsView = bot.viewById(GoalsView.VIEW_ID);
            TestUtilsUtil.activateView(goalsView);
            //list of goals
            SWTBotTable goalsTable = goalsView.bot().table();
            //check if list of goals is the same as the open goals of the proof
            assertProofGoals(proof, TestUtilsUtil.getSelectedObjects(goalsTable));
            //make sure that start auto mode button is available and stop auto mode is disabled
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            //start auto mode and wait until it is finished
            TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
            TestKeYUIUtil.waitWhileAutoMode(bot, keyEditor.getUI());
            assertProofGoals(proof, TestUtilsUtil.getSelectedObjects(goalsTable));
            TestUtilsUtil.closeView(GoalsView.VIEW_ID);
         }
      };
      doEditorTest("SWTBotGoalsViewPageTest_testGoalsView_beforeAndAfterAutoMode", 
            "data/paycard", 
            true, 
            TestKeYUIUtil.createOperationContractId("PayCard", "PayCard", "isValid()", "0", "normal_behavior"),
            5,
            false, 
            steps);
   }
   
   /**
    * tests if the selection on GoalsView works correctly.
    * @throws Exception
    */
   @Test 
   public void testGoalsView_selection() throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, KeYEnvironment<DefaultUserInterfaceControl> environment, Proof proof, SWTWorkbenchBot bot, SWTBotEditor editor, KeYEditor keyEditor) throws Exception {
            assertNotNull(keyEditor.getCurrentProof());
            assertFalse(keyEditor.getCurrentProof().closed());
            //open GoalsView
            TestUtilsUtil.openView(GoalsView.VIEW_ID);
            SWTBotView goalsView = bot.viewById(GoalsView.VIEW_ID);
            TestUtilsUtil.activateView(goalsView);
            SWTBotTable goalsTable = goalsView.bot().table();
            SWTBotView outline = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outline.bot().tree();
            //select first element on prooftree
            outlineTree.select(0);
            TableCollection selection = outlineTree.selection();
            Object[] goalsTableSelection = TestUtilsUtil.getSelectedObjects(goalsTable);
            //check if one element is selected on Outline
            assertTrue((selection.columnCount() == 1) && (selection.rowCount() == 1));
            //check if one element is selected on GoalsView
            assertEquals(goalsTableSelection.length, 1);
            //check if selection of Outline and GoalsView is synchronized
            assertSelection(TestUtilsUtil.getSelectedObjects(outlineTree), goalsTableSelection);
            //check if list of goals is correct
            assertProofGoals(proof, goalsTableSelection);
            //make sure that start auto mode button is available and stop auto mode is disabled
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            //start auto mode but apply only 2 rules
            SuspendingStopCondition sleepCondition = new SuspendingStopCondition();
            sleepCondition.setMaxRules(2);
            keyEditor.getCurrentProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(sleepCondition);
            sleepCondition.setSleep(true);
            TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
            TestKeYUIUtil.waitUntilAutoMode(bot, keyEditor.getUI());
            sleepCondition.setSleep(false);
            TestKeYUIUtil.waitWhileAutoMode(bot, keyEditor.getUI());
            //make sure that proof is not closed => there are still open goals
            assertFalse(keyEditor.getCurrentProof().closed());
            //start auto mode should still be enabled
            assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
            //make sure there are open goals on GoalsView
            goalsTableSelection = TestUtilsUtil.getSelectedObjects(goalsTable);
            assertTrue(goalsTableSelection.length > 0);
            //select first element on Outline, is no goal
            outlineTree.select(0);
            //nothing is selected on GoalsView
            goalsTableSelection = TestUtilsUtil.getSelectedObjects(goalsTable);
            assertEquals(0, goalsTableSelection.length);
            //select last element on Outline, is a goal
            outlineTree.select(outlineTree.getAllItems().length - 1);
            goalsTableSelection = TestUtilsUtil.getSelectedObjects(goalsTable);
            assertEquals(1, goalsTableSelection.length);
            //check if correct goal is selected on GoalsView
            assertSelection(TestUtilsUtil.getSelectedObjects(outlineTree), goalsTableSelection);
            TestUtilsUtil.closeView(GoalsView.VIEW_ID);
         }
      };
      doEditorTest("SWTBotGoalsViewPageTest_testGoalsView_afterAutoMode", 
            "data/paycard", 
            true, 
            TestKeYUIUtil.createOperationContractId("PayCard", "PayCard", 
                  "chargeAndRecord(int)",
                  "0", "normal_behavior"),
            5,
            false, 
            steps);
   }
   
   /**
    * tests the Goals view after manual application of rules.
    * @throws Exception
    */
   @Test
   public void testGoalsView_manualRuleApplication() throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project, KeYEnvironment<DefaultUserInterfaceControl> environment, Proof proof, SWTWorkbenchBot bot, SWTBotEditor editor, KeYEditor keyEditor) throws Exception {
            assertFalse(keyEditor.getCurrentProof().closed());
            //open GoalsView
            TestUtilsUtil.openView(GoalsView.VIEW_ID);
            SWTBotView goalsView = bot.viewById(GoalsView.VIEW_ID);
            SWTBotTable goalsTable = goalsView.bot().table();
            //check correct display of the list of goals
            assertProofGoals(proof, TestUtilsUtil.getSelectedObjects(goalsTable));
            Node node = keyEditor.getCurrentNode();
            //make sure node is not closed
            assertFalse(node.isClosed());
            //make sure node has no children
            assertEquals(0, node.childrenCount());
            final SWTBotStyledText styledText = editor.bot().styledText();
            Point point = TestUtilsUtil.selectText(styledText, "wellFormed(heap)");
            TestUtilsUtil.setCursorLocation(styledText, (int)(point.x * 0.1), point.y);
            TestUtilsUtil.clickContextMenu(styledText, point.x - 5, point.y, "impRight");
            //proof should not be closed yet
            assertFalse(keyEditor.getCurrentProof().closed());
            //node should have a child now
            assertEquals(node.childrenCount(), 1);
            assertFalse(node.isClosed());
            goalsTable = goalsView.bot().table();
            //check correct display of list of goals
            assertProofGoals(proof, TestUtilsUtil.getSelectedObjects(goalsTable));
            node = keyEditor.getCurrentNode();
            //apply another rule and check if list of goals is still correct
            point = TestUtilsUtil.selectText(styledText, "wellFormed(heap)");
            TestUtilsUtil.setCursorLocation(styledText, (int)(point.x * 0.1), point.y);
            TestUtilsUtil.clickContextMenu(styledText, point.x, point.y, "andLeft");
            assertFalse(keyEditor.getCurrentProof().closed());
            goalsTable = goalsView.bot().table();
            assertProofGoals(proof, TestUtilsUtil.getSelectedObjects(goalsTable));
            //close goalsView
            TestUtilsUtil.closeView(GoalsView.VIEW_ID);
         }
      };
      doEditorTest("SWTBotGoalsViewPageTest_testGoalsView_manualRuleApplication",
            "data/paycard", 
            true, 
            TestKeYUIUtil.createOperationContractId("PayCard", 
                  "PayCard", 
                  "isValid()", 
                  "0", 
                  "normal_behavior"),
            5,
            false, 
            steps
            );
   }
   
   /**
    * checks if the list of goals on GoalsView is the same 
    * as the open goals of the proof.
    * @param proof the current proof
    * @param listOfGoals list of goals shown on GoalsView
    */
   private void assertProofGoals(Proof proof, Object[] goals) {
      if (proof.openGoals() == null) {
         assertNull(goals);
      } else {
         assertNotNull(goals);
         if (proof.closed()) {
            assertEquals(0, goals.length);
         } else {
            Iterator<Goal> goalIt = proof.openGoals().iterator();
            assertEquals(proof.openGoals().size(), goals.length);
            for (int i = 0; i < goals.length; i++) {
               if (goalIt.hasNext()) {
                  Goal goal = goalIt.next();
                  assertEquals(goal, goals[i]);
               } else {
                  fail("More elements on GoalsView than there are open goals");
               }
            }
         }
      }
   }
   
   /**
    * check if selection on Outline is the same as the one on GoalsView.
    * @param outlineSelection selection on Outline
    * @param goalsSelection selection on GoalsView
    */
   private void assertSelection(Object[] outlineSelection, Object[] goalsSelection) {
      assertEquals(outlineSelection.length, goalsSelection.length);
      for (int i = 0; i < outlineSelection.length; i++) {
         Object outline = outlineSelection[i];
         if (outline instanceof Goal) {
            outline = ((Goal) outline).node();
         }
         Object goal = goalsSelection[i];
         if (goal instanceof Goal) {
            goal = ((Goal) goal).node();
         }
         assertSame(outline, goal);
      }
   }
}
