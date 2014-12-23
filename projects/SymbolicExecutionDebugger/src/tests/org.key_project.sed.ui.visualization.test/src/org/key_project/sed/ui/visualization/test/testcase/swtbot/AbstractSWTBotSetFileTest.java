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

package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IViewPart;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLReader;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.sed.ui.visualization.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides the basic functionality to test SET files.
 * @author Martin Hentschel
 */
public abstract class AbstractSWTBotSetFileTest extends TestCase {
   /**
    * Tests the launch of a SET file.
    * @param projectName The project Name.
    * @param pathInBundle The path in the bundle to the SET file.
    * @param pathToSetFile The path to the SET file in the created project.
    * @param additionalTestSteps Some optional additional test steps.
    * @param pathReplacements The path replacements to do.
    * @throws Exception Occurred Exception.
    */
   protected void doSetFileTest(String projectName, 
                                String pathInBundle,
                                String pathToSetFile,
                                ISetFileTestSteps additionalTestSteps,
                                PathReplacement... pathReplacements) throws Exception {
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      SWTBotTree debugTree = null;
      IViewPart propertiesView = null;
      try {
         // Create test project
         IProject project = TestUtilsUtil.createProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathInBundle, project);
         // Find SET file
         IFile setFile = project.getFile(new Path(pathToSetFile));
         assertNotNull(setFile);
         assertTrue(setFile.exists());
         // Do path replacements
         if (pathReplacements.length >= 1) {
            String setFileContent = ResourceUtil.readFrom(setFile);
            setFileContent = applyPathReplacements(project, setFileContent, pathReplacements);
            setFile.setContents(new ByteArrayInputStream(setFileContent.getBytes()), true, true, null);
         }
         // Compute path in project explorer
         List<String> uiPath = new LinkedList<String>();
         IResource current = setFile;
         while (!(current instanceof IWorkspaceRoot)) {
            uiPath.add(0, current.getName());
            current = current.getParent();
         }
         // Select SET file
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot);
         propertiesView = TestUtilsUtil.openView(IPageLayout.ID_PROP_SHEET); // Has to be opened to avoid exceptions.
         SWTBotTreeItem setFileItem = TestUtilsUtil.selectInProjectExplorer(bot, uiPath.toArray(new String[uiPath.size()]));
         setFileItem.contextMenu("Debug As").menu("&1 Symbolic Execution Tree File").click();
         // Switch into symbolic debug perspective
         TestUtilsUtil.confirmPerspectiveSwitch(bot, SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID);
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         // Compare shown tree with SET file
         SEDXMLReader reader = new SEDXMLReader();
         List<ISEDDebugTarget> expectedTargets = reader.read(setFile);
         IDebugTarget[] currentTargets = launch.getDebugTargets();
         assertEquals(expectedTargets.size(), currentTargets.length);
         int i = 0;
         for (ISEDDebugTarget expectedTarget : expectedTargets) {
            assertTrue(currentTargets[i] instanceof ISEDDebugTarget);
            TestSedCoreUtil.compareDebugTarget(expectedTarget, 
                                               (ISEDDebugTarget)currentTargets[i], 
                                               true,
                                               true,
                                               true,
                                               true);
            i++;
         }
         if (additionalTestSteps != null) {
            additionalTestSteps.test(bot, project, setFile, debugView, debugTree, launch, target);
         }
      }
      finally {
         TestUtilsUtil.openPerspective(originalPerspective);
         if (propertiesView != null) {
            TestUtilsUtil.closeView(propertiesView);
         }
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
   }
   
   /**
    * Applies the path replacements.
    * @param project The new {@link IProject}.
    * @param setFileContent The content to update.
    * @param pathReplacements The {@link PathReplacement} to apply.
    * @return The updated content.
    */
   protected String applyPathReplacements(IProject project, String setFileContent, PathReplacement... pathReplacements) {
      for (PathReplacement replacement : pathReplacements) {
         IResource resource = project.findMember(replacement.getPathToFileInWorkspace());
         assertNotNull(resource);
         assertTrue(resource.exists());
         File location = ResourceUtil.getLocation(resource);
         assertNotNull(location);
         String newPath = location.toString();
         newPath = newPath.replaceAll("\\\\", "\\\\\\\\"); // Make sure that it is a valid regular expression
         String toReplace = replacement.getPathInSetFile();
         toReplace = toReplace.replaceAll("\\\\", "\\\\\\\\"); // Make sure that it is a valid regular expression
         setFileContent = setFileContent.replaceAll(toReplace, newPath);
      }
      return setFileContent;
   }

   /**
    * A path replacement do be done in 
    * {@link AbstractSWTBotSetFileTest#doSetFileTest(String, String, String, ISetFileTestSteps)}.
    * @author Martin Hentschel
    */
   public static class PathReplacement {
      /**
       * The path in the SET file.
       */
      private final String pathInSetFile;
      
      /**
       * The path to the {@link IResource} in the workspace to replace it with its location.
       */
      private final String pathToFileInWorkspace;

      /**
       * Constructor.
       * @param pathInSetFile The path in the SET file.
       * @param pathToFileInWorkspace The path to the {@link IResource} in the workspace to replace it with its location.
       */
      public PathReplacement(String pathInSetFile, String pathToFileInWorkspace) {
         this.pathInSetFile = pathInSetFile;
         this.pathToFileInWorkspace = pathToFileInWorkspace;
      }

      /**
       * Returns the path in the SET file.
       * @return The path in the SET file.
       */
      public String getPathInSetFile() {
         return pathInSetFile;
      }

      /**
       * Returns the path to the {@link IResource} in the workspace to replace it with its location.
       * @return The path to the {@link IResource} in the workspace to replace it with its location.
       */
      public String getPathToFileInWorkspace() {
         return pathToFileInWorkspace;
      }
   }
   
   /**
    * Some additional test steps executed by 
    * {@link AbstractSWTBotSetFileTest#doSetFileTest(String, String, String, ISetFileTestSteps)}.
    * @author Martin Hentschel
    */
   public static interface ISetFileTestSteps {
      /**
       * Executes the test steps.
       * @param bot The used {@link SWTWorkbenchBot}.
       * @param project The {@link IProject} which contains the SET file.
       * @param setFile The SET file.
       * @param debugView The debug view.
       * @param debugTree The debug tree.
       * @param launch The {@link ILaunch}.
       * @param target The {@link ISEDDebugTarget}.
       */
      public void test(SWTWorkbenchBot bot,
                       IProject project,
                       IFile setFile,
                       SWTBotView debugView, 
                       SWTBotTree debugTree, 
                       ILaunch launch, 
                       ISEDDebugTarget target) throws Exception;
   }
}