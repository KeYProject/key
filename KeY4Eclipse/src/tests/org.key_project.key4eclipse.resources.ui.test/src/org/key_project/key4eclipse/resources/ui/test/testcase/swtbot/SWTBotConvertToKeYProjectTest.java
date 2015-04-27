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

package org.key_project.key4eclipse.resources.ui.test.testcase.swtbot;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IViewPart;
import org.junit.Test;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.key4eclipse.resources.ui.handler.ConvertJavaToKeYProjectHandler;
import org.key_project.key4eclipse.resources.ui.test.util.KeY4EclipseResourcesUiTestUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link ConvertJavaToKeYProjectHandler}.
 * @author Martin Hentschel
 */
public class SWTBotConvertToKeYProjectTest extends AbstractSetupTestCase {   
   /**
    * Creates a new {@link IJavaProject} and converts it into a KeYProject. The used view is the ProjectExplorer.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testConvertToKeYProjectInProjectExplorer() throws Exception {
      doTest("SWTBotConvertToKeYProjectTest_testConvertToKeYProjectInProjectExplorer", 
             IPageLayout.ID_PROJECT_EXPLORER);
   }
   
   /**
    * Creates a new {@link IJavaProject} and converts it into a KeYProject. The used view is the PackageExplorer.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testConvertToKeYProjectInPackageExplorer() throws Exception {
      doTest("SWTBotConvertToKeYProjectTest_testConvertToKeYProjectInPackageExplorer", 
             JavaUI.ID_PACKAGES);
   }
   
   /**
    * Creates a new {@link IJavaProject} and converts it into a KeYProject. The used view is the ProjectNavigator.
    * @throws Exception Occurred Exception.
    */
   @SuppressWarnings("deprecation")
   @Test
   public void testConvertToKeYProjectInNavigator() throws Exception {
      doTest("SWTBotConvertToKeYProjectTest_testConvertToKeYProjectInNavigator", 
             IPageLayout.ID_RES_NAV);
   }
   
   /**
    * Executes the test steps.
    * @param projectName The name of the workspace project to create and to convert.
    * @param viewId The ID of the view.
    * @throws Exception Occurred Exception.
    */
   protected void doTest(String projectName, String viewId) throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
      IViewPart alreadyOpenedView = TestUtilsUtil.findView(viewId);
      if (alreadyOpenedView == null) {
         TestUtilsUtil.openView(viewId);
      }
      try {
         SWTBotView view = bot.viewById(viewId);
         TestUtilsUtil.selectInTree(view.bot().tree(), project.getProject().getName());
         TestUtilsUtil.clickContextMenu(view.bot().tree(), "Convert to KeY Project");
         KeY4EclipseResourcesTestUtil.waitBuild();
         KeY4EclipseResourcesUiTestUtil.assertKeYNature(project.getProject());
      }
      finally {
         if (alreadyOpenedView == null) {
            TestUtilsUtil.closeView(viewId);
         }
      }
   }
}