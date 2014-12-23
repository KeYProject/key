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
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

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

      final Set<String> BROKEN_PROOF_FILE_PATHES = new HashSet<String>();
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML operation contract (id_ 9 - Transaction__Transaction).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML operation contract (id_ 8 - Transaction__getTotal).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML operation contract (id_ 6 - Main__main).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML operation contract (id_ 5 - Account__Account).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML operation contract (id_ 4 - Account__getTotal).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML operation contract (id_ 3 - Account__transfer).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML operation contract (id_ 2 - Account__withdraw).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML operation contract (id_ 1 - Account__deposit).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML depends clause (id_ 7 - java.lang.Object___inv_ for Transaction).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_project/JML depends clause (id_ 0 - java.lang.Object___inv_ for Account).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_List with Sequences_project/LinkedList(LinkedList__remove(java.lang.Object)).JML normal_behavior operation contract.1.proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_4 - N Queens_project/Queens_search.proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_5 - Red-Black Trees_project/project.key");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Declassification - Sum_project/project.key");

      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML operation contract (id_ 9 - Transaction__Transaction).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML operation contract (id_ 8 - Transaction__getTotal).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML operation contract (id_ 6 - Main__main).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML operation contract (id_ 5 - Account__Account).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML operation contract (id_ 4 - Account__getTotal).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML operation contract (id_ 3 - Account__transfer).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML operation contract (id_ 2 - Account__withdraw).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML operation contract (id_ 1 - Account__deposit).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML depends clause (id_ 7 - java.lang.Object___inv_ for Transaction).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Transaction_src/JML depends clause (id_ 0 - java.lang.Object___inv_ for Account).proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_List with Sequences_src/LinkedList(LinkedList__remove(java.lang.Object)).JML normal_behavior operation contract.1.proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_4 - N Queens_src/Queens_search.proof");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_5 - Red-Black Trees_src/project.key");
      BROKEN_PROOF_FILE_PATHES.add("/SWTBotKeYExampleNewWizardTest_Declassification - Sum_src/project.key");
      
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Close welcome view
      TestUtilsUtil.closeWelcomeView(bot);
      // Get examples
      File examplesDir = new File(Main.getExamplesDir());
      List<ExampleChooser.Example> examples = ExampleChooser.listExamples(examplesDir);
      for (final ExampleChooser.Example example : examples) {
         // Open wizard
         bot.menu("File").menu("New").menu("Example...").click();
         SWTBotShell newWizard = bot.shell("New Example");
         // Select new wizard
         TestUtilsUtil.selectInTree(newWizard.bot().tree(), "KeY", "KeY Example");
         TestUtilsUtil.clickDirectly(newWizard.bot().button("Next >"));
         // Select example to create
         String[] path = example.getPath();
         path = ArrayUtil.add(path, example.getName());
         TestUtilsUtil.selectInTree(newWizard.bot().tree(), path);
         // Test shown tabs
         newWizard.bot().tabItem("Description").activate();
         assertEquals(example.getDescription(), newWizard.bot().text().getText());
         if (IOUtil.exists(example.getObligationFile())) {
            newWizard.bot().tabItem("Proof Obligation").activate();
            TestUtilsUtil.assertEqualsIgnoreWhiteSpace(IOUtil.readFrom(example.getObligationFile()), newWizard.bot().styledText().getText());
         }
         for (File additionalFile : example.getAdditionalFiles()) {
            if (IOUtil.exists(additionalFile)) {
               newWizard.bot().tabItem(additionalFile.getName()).activate();
               TestUtilsUtil.assertEqualsIgnoreWhiteSpace(IOUtil.readFrom(additionalFile), newWizard.bot().styledText().getText());
            }
         }
         // Select next wizard page
         TestUtilsUtil.clickDirectly(newWizard.bot().button("Next >"));
         // Make sure that project name is valid and change it
         assertEquals(example.getName(), newWizard.bot().text().getText());
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
         // Make sure that all example files and folders are copied into project (hierarchy and file content might have changed)
         final Set<String> fileNames = new HashSet<String>();
         if (KeYExampleNewWizard.ONLY_SPECIFIED_EXAMPLE_CONTENT) {
            for (File file : example.getAdditionalFiles()) {
               fileNames.add(file.getName());
            }
            for (File file : example.getExportFiles()) {
               fileNames.add(file.getName());
            }
            if (IOUtil.exists(example.getObligationFile())) {
               fileNames.add(example.getObligationFile().getName());
            }
            if (IOUtil.exists(example.getExampleFile())) {
               fileNames.add(example.getExampleFile().getName());
            }
            if (IOUtil.exists(example.getProofFile())) {
               fileNames.add(example.getProofFile().getName());
            }
         }
         else {
            IOUtil.visit(example.getDirectory(), new IOUtil.IFileVisitor() {
               @Override
               public void visit(File file) {
                  if (file.isFile()) {
                     fileNames.add(file.getName());
                  }
               }
            });
         }
         project.accept(new IResourceVisitor() {
            @Override
            public boolean visit(IResource resource) throws CoreException {
               fileNames.remove(resource.getName());
               return true;
            }
         });
         assertTrue("Missing files: " + CollectionUtil.toString(fileNames) + " of example \"" + example.getName() + "\".", fileNames.isEmpty());
         // Make sure that the project can be compiled
         if (!EXAMPLES_WITH_COMPILER_FAILURES.contains(example.getName())) {
            IMarker[] problems = project.findMarkers(IJavaModelMarker.JAVA_MODEL_PROBLEM_MARKER, true, IResource.DEPTH_INFINITE);
            for (IMarker marker : problems) {
               Integer severityType = (Integer) marker.getAttribute(IMarker.SEVERITY);
               if (severityType.intValue() == IMarker.SEVERITY_ERROR) {
                  fail("Problems available at example \"" + example.getName() + "\": " + marker.getAttributes());
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
                     if (!BROKEN_PROOF_FILE_PATHES.contains(resource.getFullPath().toString())) {
                        KeYEnvironment<CustomUserInterface> env = KeYEnvironment.load(location, classPaths, bootClassPath);
                        env.dispose();
                     }
                  }
                  catch (Exception e) {
                     System.out.println("Broken: " + resource.getFullPath().toString());
                     fail("Loading of " + resource + " failed in example \"" + example.getName() + "\" stored in \"" + example.getDirectory() + "\".");
                  }
               }
               return true;
            }
         });
      }
   }
}