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

package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import java.io.File;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaModelMarker;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.wizard.KeYExampleNewWizard;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.util.KeYExampleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * SWTBot tests for {@link KeYExampleNewWizard}.
 * @author Martin Hentschel
 */
public class SWTBotKeYExampleNewWizardTest extends AbstractSetupTestCase {
   /**
    * Makes sure that all examples can be created.
    */
   @Test
   public void testAllExamples_InProject() throws Exception {
      doTestAllExamples(false);
   }
   
   /**
    * Makes sure that all examples can be created.
    */
   @Test
   public void testAllExamples_InSourceDir() throws Exception {
      doTestAllExamples(true);
   }
      
   /**
    * Executes the test steps of {@link #testAllExamples_InProject()} and
    * {@link #testAllExamples_InSourceDir()}.
    * @param srcDir {@code true} in source directory, {@code false} in project.
    * @throws Exception Occurred Exception.
    */
   protected void doTestAllExamples(boolean srcDir) throws Exception {
      final Set<String> EXAMPLES_WITH_COMPILER_FAILURES = new HashSet<String>();
      EXAMPLES_WITH_COMPILER_FAILURES.add("Java5");
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Close welcome view
      TestUtilsUtil.closeWelcomeView(bot);
      int examplesCount = -1;
      int i = 0;
      do {
         // Open wizard
         bot.menu("File").menu("New").menu("Example...").click();
         SWTBotShell newWizard = bot.shell("New Example");
         // Select new wizard
         TestUtilsUtil.selectInTree(newWizard.bot().tree(), "KeY", "KeY Example");
         TestUtilsUtil.clickDirectly(newWizard.bot().button("Next >"));
         // Test number of examples
         if (examplesCount < 0) {
            examplesCount = newWizard.bot().list().getItems().length;
            assertTrue("No examples available.", examplesCount >= 1);
         }
         else {
            assertEquals(examplesCount, newWizard.bot().list().getItems().length);
         }
         // Select example to create
         newWizard.bot().list().select(i);
         final String example = newWizard.bot().list().selection()[0];
         TestUtilsUtil.clickDirectly(newWizard.bot().button("Next >"));
         // Make sure that project name is valid and change it
         assertEquals(example, newWizard.bot().text().getText());
         String projectName = "SWTBotKeYExampleNewWizardTest_" + example + (srcDir ? "_src" : "_project");
         if (srcDir) {
            newWizard.bot().radio("Create separate folders for sources and class files").click();
         }
         else {
            newWizard.bot().radio("Use project folder as root for sources and class files").click();
         }
         newWizard.bot().text().setText(projectName);
         // Finish wizard
         TestUtilsUtil.clickDirectly(newWizard.bot().button("Finish"));
         // Close perspective switch dialog
         bot.shell("Open Associated Perspective?").bot().button("No").click();
         TestUtilsUtil.waitForBuild();
         // Make sure that project was created
         IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
         assertTrue(project.exists());
         assertTrue(project.isOpen());
         // Find example directory
         File[] examples = new File(KeYExampleUtil.getLocalExampleDirectory()).listFiles();
         final File exampleDirectory = ArrayUtil.search(examples, new IFilter<File>() {
            @Override
            public boolean select(File element) {
               return element.getName().endsWith(example);
            }
         });
         assertNotNull(exampleDirectory);
         // Make sure that all example files and folders are copied into project (hierarchy and file content might have changed)
         final Set<String> fileNames = new HashSet<String>();
         IOUtil.visit(exampleDirectory, new IOUtil.IFileVisitor() {
            @Override
            public void visit(File file) {
               if (file.isFile()) {
                  fileNames.add(file.getName());
               }
            }
         });
         project.accept(new IResourceVisitor() {
            @Override
            public boolean visit(IResource resource) throws CoreException {
               fileNames.remove(resource.getName());
               return true;
            }
         });
         assertTrue("Missing files: " + CollectionUtil.toString(fileNames) + " of example \"" + example + "\".", fileNames.isEmpty());
         i++;
         // Make sure that the project can be compiled
         if (!EXAMPLES_WITH_COMPILER_FAILURES.contains(example)) {
            IMarker[] problems = project.findMarkers(IJavaModelMarker.JAVA_MODEL_PROBLEM_MARKER, true, IResource.DEPTH_INFINITE);
            for (IMarker marker : problems) {
               Integer severityType = (Integer) marker.getAttribute(IMarker.SEVERITY);
               if (severityType.intValue() == IMarker.SEVERITY_ERROR) {
                  fail("Problems available at example \"" + example + "\": " + marker.getAttributes());
               }
            }
         }
         // Make sure that *.key and *.proof files are valid
         final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
         final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
         project.accept(new IResourceVisitor() {
            @Override
            public boolean visit(IResource resource) throws CoreException {
               String extension = resource.getFileExtension();
               if (KeYUtil.isFileExtensionSupported(extension)) {
                  File location = ResourceUtil.getLocation(resource);
                  Assert.isNotNull(location);
                  Assert.isTrue(location.exists());
                  try {
                     KeYEnvironment<CustomConsoleUserInterface> env = KeYEnvironment.load(location, classPaths, bootClassPath);
                     env.dispose();
                  }
                  catch (Exception e) {
                     fail("Loading of " + resource + " failed in example \"" + example + "\".");
                  }
               }
               return true;
            }
         });
      }
      while (i < examplesCount);
   }
}