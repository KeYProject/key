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

package org.key_project.sed.ui.test.testcase.swtbot;

import org.eclipse.debug.core.model.IVariable;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;

/**
 * Tests the property page tab "Variable".
 * @author Martin Hentschel
 */
public class SWTBotVariablesTabTest extends AbstractSWTBotVariablesPropertyTabTest {
   /**
    * Tests the shown values and the existence of tab "Variable".
    */
   @Test
   public void testValuesAndTabExistence() throws Exception {
      doFixedExampleTest(createFixedExampleSteps());
   }
   
   /**
    * Creates the test steps to execute.
    * @return The created test steps.
    */
   public static ITestSteps createFixedExampleSteps() {
      return new AbstractTestSteps() {
         @Override
         public void assertFirstVariable(SWTBotTree variablesTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, IVariable firstVariable) {
            assertTrue(tabs.selectTabItem("Variable"));
            assertEquals("var1", propertiesView.bot().text(0).getText());
            assertEquals("var1type", propertiesView.bot().text(1).getText());
            assertEquals("s1var1value", propertiesView.bot().text(2).getText());
            assertEquals("s1var1valueType", propertiesView.bot().text(3).getText());
         }

         @Override
         public void assertSecondVariable(SWTBotTree variablesTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, IVariable variable) {
            assertTrue(tabs.selectTabItem("Variable"));
            assertEquals("var2", propertiesView.bot().text(0).getText());
            assertEquals("var2type", propertiesView.bot().text(1).getText());
            assertEquals("s1var2value", propertiesView.bot().text(2).getText());
            assertEquals("s1var2valueType", propertiesView.bot().text(3).getText());
         }

         @Override
         public void assertNoVariable(SWTBotTree variablesTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) {
            assertFalse(tabs.selectTabItem("Variable"));
         }
      };
   }
}