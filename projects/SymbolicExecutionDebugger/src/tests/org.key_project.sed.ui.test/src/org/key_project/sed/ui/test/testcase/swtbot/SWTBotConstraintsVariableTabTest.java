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
import org.key_project.sed.ui.util.SEDUIPreferenceUtil;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;

/**
 * Tests the property page tab "Constraints".
 * @author Martin Hentschel
 */
public class SWTBotConstraintsVariableTabTest extends AbstractSWTBotVariablesPropertyTabTest {
   /**
    * Tests the shown values and the existence of tab "Constraints".
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
            assertTrue(tabs.selectTabItem("Constraints"));
            doTestConstraints(propertiesView);
         }

         @Override
         public void assertSecondVariable(SWTBotTree variablesTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, IVariable variable) {
            assertTrue(tabs.selectTabItem("Constraints"));
            doTestConstraints(propertiesView);
         }
         
         protected void doTestConstraints(SWTBotView propertiesView) {
            // Test initial
            if (SEDUIPreferenceUtil.isShowAllConstraints()) {
               assertEquals(4, propertiesView.bot().table().rowCount());
            }
            else {
               assertEquals(1, propertiesView.bot().table().rowCount());
            }
            // Toggle shown content
            SEDUIPreferenceUtil.setShowAllConstraints(!SEDUIPreferenceUtil.isShowAllConstraints());
            if (SEDUIPreferenceUtil.isShowAllConstraints()) {
               assertEquals(4, propertiesView.bot().table().rowCount());
            }
            else {
               assertEquals(1, propertiesView.bot().table().rowCount());
            }
            // Toggle shown content again
            SEDUIPreferenceUtil.setShowAllConstraints(!SEDUIPreferenceUtil.isShowAllConstraints());
            if (SEDUIPreferenceUtil.isShowAllConstraints()) {
               assertEquals(4, propertiesView.bot().table().rowCount());
            }
            else {
               assertEquals(1, propertiesView.bot().table().rowCount());
            }
         }

         @Override
         public void assertNoVariable(SWTBotTree variablesTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) {
            assertFalse(tabs.selectTabItem("Variable"));
         }
      };
   }
}