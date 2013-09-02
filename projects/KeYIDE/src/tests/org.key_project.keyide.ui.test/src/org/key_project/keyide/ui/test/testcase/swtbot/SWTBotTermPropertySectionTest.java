package org.key_project.keyide.ui.test.testcase.swtbot;

import java.util.Collections;

import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.junit.Test;
import org.key_project.key4eclipse.test.util.TestKeY4EclipseUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.property.TermPropertySection;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;

/**
 * SWTBot tests for {@link TermPropertySection}.
 * @author Martin Hentschel
 */
public class SWTBotTermPropertySectionTest extends AbstractSWTBotKeYEditorPropertiesTest {
   /**
    * Tests the shown values on different selected nodes.
    */
   @Test
   public void testValuesOnDifferentNodes_Editor() throws Exception {
      doPropertiesTest("SWTBotTermPropertySectionTest_testValuesOnDifferentNodes_Editor", 
                       "data/paycard",
                       TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "isValid()", "0", "normal_behavior"),
                       false,
                       createSteps());
   }
   /**
    * Tests the shown values on different selected nodes.
    */
   @Test
   public void testValuesOnDifferentNodes_OutlineView() throws Exception {
      doPropertiesTest("SWTBotTermPropertySectionTest_testValuesOnDifferentNodes_PropertiesView", 
                       "data/paycard",
                       TestKeY4EclipseUtil.createOperationContractId("PayCard", "PayCard", "isValid()", "0", "normal_behavior"),
                       true,
                       createSteps());
   }
   
   /**
    * Creates the test steps.
    * @return The {@link IPropertiesTestSteps} to execute.
    */
   protected IPropertiesTestSteps createSteps() {
      return new IPropertiesTestSteps() {
         @Override
         public void assertNodeTab(SWTBotEditor editor,
                                   KeYEditor keyEditor,
                                   SWTBotView propertiesView, 
                                   KeYMediator mediator, 
                                   Node node) throws Exception {
            assertTermTab(propertiesView, mediator, keyEditor.getSelectedPosInSequent());
            TestUtilsUtil.setCursorLocation(editor.bot().styledText(), 8, 8);
            assertTermTab(propertiesView, mediator, keyEditor.getSelectedPosInSequent());
            TestUtilsUtil.setCursorLocation(editor.bot().styledText(), 0, 0);
            assertTermTab(propertiesView, mediator, keyEditor.getSelectedPosInSequent());
            TestUtilsUtil.setCursorLocation(editor.bot().styledText(), 8, 100);
            assertTermTab(propertiesView, mediator, keyEditor.getSelectedPosInSequent());
         }
      };
   }
   
   /**
    * Tests the shown {@link PosInSequent}.
    * @param propertiesView The properties view.
    * @param mediator The {@link KeYMediator} to use.
    * @param pis The expected shown {@link PosInSequent}.
    */
   protected void assertTermTab(SWTBotView propertiesView, 
                                KeYMediator mediator, 
                                PosInSequent pis) {
      SWTBotTabbedPropertyList tabs = getPropertiesTabs(propertiesView);
      assertTrue(tabs.hasTabItem("Term"));
      assertTrue(tabs.selectTabItem("Term"));
      if (pis != null) {
         assertEquals(validate(TermPropertySection.posInSequentToString(pis)), propertiesView.bot().text(0).getText());
      }
      else {
         assertEquals(StringUtil.EMPTY_STRING, propertiesView.bot().text(0).getText());
      }
      if (pis != null && pis.getPosInOccurrence() != null) {
         Term term = pis.getPosInOccurrence().subTerm();
         assertEquals(validate(ObjectUtil.toString(term.sort())), propertiesView.bot().text(1).getText());
         assertEquals(validate(TermPropertySection.operatorToString(term.op())), propertiesView.bot().text(2).getText());
         assertList(term.subs(), propertiesView.bot().list(0));
         assertList(term.freeVars(), propertiesView.bot().list(1));
         assertList(term.boundVars(), propertiesView.bot().list(2));
         assertEquals(validate(ObjectUtil.toString(term.javaBlock())), propertiesView.bot().text(3).getText());
         assertList(term.getLabels(), propertiesView.bot().list(3));
         assertEquals(validate(term.hashCode() + StringUtil.EMPTY_STRING), propertiesView.bot().text(4).getText());
      }
      else {
         assertEquals(StringUtil.EMPTY_STRING, propertiesView.bot().text(1).getText());
         assertEquals(StringUtil.EMPTY_STRING, propertiesView.bot().text(2).getText());
         assertList(Collections.EMPTY_LIST, propertiesView.bot().list(0));
         assertList(Collections.EMPTY_LIST, propertiesView.bot().list(1));
         assertList(Collections.EMPTY_LIST, propertiesView.bot().list(2));
         assertEquals(StringUtil.EMPTY_STRING, propertiesView.bot().text(3).getText());
         assertList(Collections.EMPTY_LIST, propertiesView.bot().list(3));
         assertEquals(StringUtil.EMPTY_STRING, propertiesView.bot().text(4).getText());
      }
   }
}
