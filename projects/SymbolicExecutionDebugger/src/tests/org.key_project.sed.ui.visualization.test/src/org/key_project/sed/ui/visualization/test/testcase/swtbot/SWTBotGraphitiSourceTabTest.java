package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.junit.Test;
import org.key_project.sed.ui.test.testcase.swtbot.SWTBotSourceTabTest;
import org.key_project.sed.ui.test.util.SWTBotTabbedPropertyList;

/**
 * Tests the property page tab "Source" in a Symbolic Execution Tree diagram.
 * @author Martin Hentschel
 */
public class SWTBotGraphitiSourceTabTest extends AbstractSWTBotGraphitiPropertyTabTest {
   /**
    * Tests the shown values and the existence of tab "Source".
    */
   @Test
   public void testValuesAndTabExistence() throws Exception {
      doFixedExampleTest(SWTBotSourceTabTest.createFixedExampleSteps());
   }
   
   /**
    * Tests the tab "Source" in an symbolic execution tree diagram
    * which is opened editable in an editor.
    */
   @Test
   public void testInDiagramEditor() throws Exception {
      doInDiagramEditorTest(new IEditorTestSteps() {
         @Override
         public void assertThread(SWTBotGefEditor editor, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Source"));
         }
         
         @Override
         public void assertStatement(SWTBotGefEditor editor, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Source"));
         }
         
         @Override
         public void assertDiagram(SWTBotGefEditor editor, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Source"));
         }
      });
   }
}
