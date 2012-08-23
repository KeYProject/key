package org.key_project.sed.key.ui.test.testcase.swtbot;

import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.ui.test.util.SWTBotTabbedPropertyList;

/**
 * Tests the property page tab "KeY".
 * @author Martin Hentschel
 */
public class SWTBotKeYTabTest extends AbstractSWTBotKeYPropertyTabTest {
   /**
    * Tests the shown values and the existence of tab "KeY".
    */
   @Test
   public void testValuesAndTabExistence() throws Exception {
      doFlatStepsTest("SWTBotKeYTabTest_testValuesAndTabExistence", createFixedExampleSteps());
   }
   
   /**
    * Creates the test steps to execute.
    * @return The created test steps.
    */
   public static ITestSteps createFixedExampleSteps() {
      return new ITestSteps() {
         @Override
         public void assertThread(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertTrue(tabs.selectTabItem("KeY"));
            assertFalse(propertiesView.bot().text(0).getText().isEmpty());
            assertFalse(propertiesView.bot().text(1).getText().isEmpty());
         }
         
         @Override
         public void assertStatement(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertTrue(tabs.selectTabItem("KeY"));
            assertFalse(propertiesView.bot().text(0).getText().isEmpty());
            assertFalse(propertiesView.bot().text(1).getText().isEmpty());
         }
         
         @Override
         public void assertDebugTarget(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("KeY"));
         }

         @Override
         public void assertMethodReturn(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertTrue(tabs.selectTabItem("KeY"));
            assertFalse(propertiesView.bot().text(0).getText().isEmpty());
            assertFalse(propertiesView.bot().text(1).getText().isEmpty());
         }

         @Override
         public void assertLaunch(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("KeY"));
         }
      };
   }
}
