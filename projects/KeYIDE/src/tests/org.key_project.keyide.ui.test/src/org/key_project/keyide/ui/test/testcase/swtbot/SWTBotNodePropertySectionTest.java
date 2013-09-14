package org.key_project.keyide.ui.test.testcase.swtbot;

import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.key4eclipse.test.util.TestKeY4EclipseUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.property.NodePropertySection;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Node;

/**
 * SWTBot tests for {@link NodePropertySection}.
 * @author Martin Hentschel
 */
public class SWTBotNodePropertySectionTest extends AbstractSWTBotKeYEditorPropertiesTest {
   /**
    * Tests the shown values on different selected nodes.
    */
   @Test
   public void testValuesOnDifferentNodes_Editor() throws Exception {
      doPropertiesTest("SWTBotNodePropertySectionTest_testValuesOnDifferentNodes_Editor", 
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
      doPropertiesTest("SWTBotNodePropertySectionTest_testValuesOnDifferentNodes_PropertiesView", 
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
            SWTBotTabbedPropertyList tabs = getPropertiesTabs(propertiesView);
            assertTrue(tabs.hasTabItem("Node"));
            assertTrue(tabs.selectTabItem("Node"));
            assertEquals(validate(ProofTreeLabelProvider.getNodeText(node)), propertiesView.bot().text(0).getText());
            assertEquals(validate(ProofSourceViewerDecorator.ruleToString(mediator, node.getAppliedRuleApp(), false)), propertiesView.bot().text(1).getText());
            assertEquals(node.getNodeInfo().getInteractiveRuleApplication(), propertiesView.bot().checkBox(0).isChecked());
            assertEquals(node.isClosed(), propertiesView.bot().checkBox(1).isChecked());
            assertEquals(validate(node.getNodeInfo().getFirstStatementString()), propertiesView.bot().text(2).getText());
            assertEquals(validate(ObjectUtil.toString(node.getNodeInfo().getActiveStatement())), propertiesView.bot().text(3).getText());
            assertEquals(validate(ObjectUtil.toString(node.getNodeInfo().getExecStatementParentClass())), propertiesView.bot().text(4).getText());
            assertEquals(validate(ObjectUtil.toString(node.getNodeInfo().getExecStatementPosition())), propertiesView.bot().text(5).getText());
            assertEquals(validate(ObjectUtil.toString(node.countBranches())), propertiesView.bot().text(6).getText());
            assertEquals(validate(ObjectUtil.toString(node.countNodes())), propertiesView.bot().text(7).getText());
            assertList(node.getGlobalProgVars(), propertiesView.bot().list(0));
            assertList(node.getLocalIntroducedRules(), propertiesView.bot().list(1));
            assertList(node.getRenamingTable(), propertiesView.bot().list(2));
         }
      };
   }
}
