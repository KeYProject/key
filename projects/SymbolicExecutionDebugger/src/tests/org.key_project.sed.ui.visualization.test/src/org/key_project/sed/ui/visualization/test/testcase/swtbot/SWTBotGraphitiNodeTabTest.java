package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.junit.Test;
import org.key_project.sed.ui.test.testcase.swtbot.SWTBotNodeTabTest;
import org.key_project.sed.ui.test.util.SWTBotTabbedPropertyList;

/**
 * Tests the property page tab "Node" in a Symbolic Execution Tree diagram.
 * @author Martin Hentschel
 */
public class SWTBotGraphitiNodeTabTest extends AbstractSWTBotGraphitiPropertyTabTest {
   /**
    * Tests the shown values and the existence of tab "Node".
    */
   @Test
   public void testValuesAndTabExistence() throws Exception {
      doFixedExampleTest(SWTBotNodeTabTest.createFixedExampleSteps());
   }
   
   /**
    * Tests the tab "Node" in an symbolic execution tree diagram
    * which is opened editable in an editor.
    */
   @Test
   public void testInDiagramEditor() throws Exception {
      doInDiagramEditorTest(new IEditorTestSteps() {
         @Override
         public void assertThread(SWTBotGefEditor editor, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertTrue(tabs.selectTabItem("Node"));
            assertEquals("<start>", propertiesView.bot().text(0).getText());
            assertEquals("true", propertiesView.bot().text(1).getText());
         }
         
         @Override
         public void assertStatement(SWTBotGefEditor editor, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertTrue(tabs.selectTabItem("Node"));
            assertEquals("int x = 1;", propertiesView.bot().text(0).getText());
            assertEquals("true", propertiesView.bot().text(1).getText());
         }
         
         @Override
         public void assertDiagram(SWTBotGefEditor editor, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception {
            assertFalse(tabs.hasTabItem("Node"));
         }
      });
   }
}
