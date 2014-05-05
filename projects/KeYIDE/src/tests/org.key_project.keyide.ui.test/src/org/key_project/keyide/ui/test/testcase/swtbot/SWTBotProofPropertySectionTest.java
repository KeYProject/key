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

import java.util.List;

import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.junit.Test;
import org.key_project.key4eclipse.test.util.TestKeY4EclipseUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.property.ProofPropertySection;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Pair;

/**
 * SWTBot tests for {@link ProofPropertySection}.
 * @author Martin Hentschel
 */
public class SWTBotProofPropertySectionTest extends AbstractSWTBotKeYEditorPropertiesTest {
   /**
    * Tests the shown values on different selected nodes.
    */
   @Test
   public void testValuesOnDifferentNodes_Editor() throws Exception {
      doPropertiesTest("SWTBotProofPropertySectionTest_testValuesOnDifferentNodes_Editor", 
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
      doPropertiesTest("SWTBotProofPropertySectionTest_testValuesOnDifferentNodes_PropertiesView", 
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
            assertTrue(tabs.hasTabItem("Proof"));
            assertTrue(tabs.selectTabItem("Proof"));
            List<Pair<String, String>> summary = node.proof().statistics().getSummary();
            int i = 0;
            for (Pair<String, String> pair : summary) {
               assertEquals(validate(pair.first), propertiesView.bot().clabel(i).getText());
               assertEquals(validate(pair.second), propertiesView.bot().text(i).getText());
               i++;
            }
         }
      };
   }
}