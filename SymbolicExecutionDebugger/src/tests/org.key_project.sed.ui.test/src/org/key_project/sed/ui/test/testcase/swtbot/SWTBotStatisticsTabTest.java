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

import org.eclipse.debug.core.ILaunch;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISEStatement;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests the property page tab "Statistics".
 * @author Martin Hentschel
 */
public class SWTBotStatisticsTabTest extends AbstractSWTBotPropertyTabTest {
   /**
    * Tests the shown values and the existence of tab "Node".
    */
   @Test
   public void testValuesAndTabExistence() throws Exception {
      doFixedExampleTest(createFixedExampleSteps(false));
   }
   
   /**
    * Creates the test steps to execute.
    * @return The created test steps.
    */
   public static ITestSteps createFixedExampleSteps(final boolean diagramProperties) {
      return new ITestSteps() {
         @Override
         public void initializeLaunch(ILaunch launch) throws Exception {
         }
         
         @Override
         public void assertThread(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEThread thread) throws Exception {
            assertFalse(tabs.hasTabItem("Statistics"));
         }
         
         @Override
         public void assertStatement(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEStatement statement) throws Exception {
            assertFalse(tabs.hasTabItem("Statistics"));
         }
         
         @Override
         public void assertDebugTarget(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDebugTarget target) throws Exception {
            assertTrue(tabs.hasTabItem("Statistics"));
            tabs.selectTabItem("Statistics");
            propertiesView.setFocus();
            TestUtilsUtil.waitForJobs();            
            assertEquals("18", propertiesView.bot().text(0).getText());
            assertEquals("2", propertiesView.bot().text(1).getText());
            assertEquals("3", propertiesView.bot().text(2).getText());
            assertEquals("0", propertiesView.bot().text(3).getText());
         }

         @Override
         public void assertMethodReturn(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEMethodReturn methodReturn) throws Exception {
            assertFalse(tabs.hasTabItem("Statistics"));
         }

         @Override
         public void assertMethodCall(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEMethodCall methodCall) throws Exception {
            assertFalse(tabs.hasTabItem("Statistics"));
         }
      };
   }
}