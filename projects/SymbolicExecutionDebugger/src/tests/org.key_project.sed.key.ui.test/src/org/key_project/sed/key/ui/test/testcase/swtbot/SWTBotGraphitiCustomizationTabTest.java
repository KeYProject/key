package org.key_project.sed.key.ui.test.testcase.swtbot;

import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.ui.test.util.SWTBotTabbedPropertyList;

/**
 * Tests the property page tab "Customization" in a Symbolic Execution Tree diagram.
 * @author Martin Hentschel
 */
public class SWTBotGraphitiCustomizationTabTest extends AbstractSWTBotGraphitiKeYPropertyTabTest {
   /**
    * Tests the shown values and the existence of tab "Customization".
    */
   @Test
   public void testValuesAndTabExistence() throws Exception {
      doFlatStepsTest("SWTBotGraphitiCustomizationTabTest_testValuesAndTabExistence", new ITestSteps() {
         @Override
         public void assertThread(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Customization"));
         }

         @Override
         public void assertStatement(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Customization"));
         }

         @Override
         public void assertDebugTarget(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Customization"));
         }

         @Override
         public void assertMethodReturn(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Customization"));
         }

         @Override
         public void assertLaunch(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Customization"));
         }
      });
   }
   
   /**
    * Tests the tab "Customization" in an symbolic execution tree diagram
    * which is opened editable in an editor.
    */
   @Test
   public void testInDiagramEditor() throws Exception {
      doInDiagramEditorTest(new IEditorTestSteps() {
         @Override
         public void assertThread(SWTBotGefEditor editor, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Main"));
         }
         
         @Override
         public void assertStatement(SWTBotGefEditor editor, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Main"));
         }
         
         @Override
         public void assertDiagram(SWTBotGefEditor editor, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Main"));
         }
      });
   }
}
