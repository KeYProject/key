/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.sed.key.core.test.testcase.swtbot;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.key.core.launch.KeYSourceLookupParticipant;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.sed.key.ui.view.SymbolicExecutionSettingsView;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

/**
 * SWTBot tests for {@link KeYSourceLookupParticipant}.
 * @author Martin Hentschel
 */
public class SWTBotKeYSourceLookupParticipantTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests a class named {@code SameName} in different packages.
    * @throws Exception Occurred Exception
    */
   public void testResourceFindingWithSameNames() throws Exception {
      IProjectConfigurator configurator = new IProjectConfigurator() {
         @Override
         public void configure(IJavaProject javaProject) throws Exception {
            IProject project = javaProject.getProject();
            // Create boot folder
            IFolder bootFolder = TestUtilsUtil.createFolder(project, "boot");
            BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/sameNamesSourceLocationTest/boot", bootFolder);
            KeYResourceProperties.setBootClassPath(project, bootFolder.getFullPath().toString());
            KeYResourceProperties.setUseBootClassPathKind(project, UseBootClassPathKind.WORKSPACE);
            // Create specs folder
            IFolder specsFolder = TestUtilsUtil.createFolder(project, "specs");
            BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/sameNamesSourceLocationTest/specs", specsFolder);
            List<KeYClassPathEntry> entries = new LinkedList<KeYClassPathEntry>();
            entries.add(new KeYClassPathEntry(KeYClassPathEntryKind.WORKSPACE, specsFolder.getFullPath().toString()));
            KeYResourceProperties.setClassPathEntries(project, entries);
         }
      };
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            IFolder srcFolder = project.getProject().getFolder("src");
            IFile mainFile = srcFolder.getFile("Main.java");
            IFile defaultFile = srcFolder.getFile("SameName.java");
            IFile aFile = srcFolder.getFolder("a").getFile("SameName.java");
            IFile aSubFile = srcFolder.getFolder("a").getFolder("sub").getFile("SameName.java");
            IFile bFile = srcFolder.getFolder("b").getFile("SameName.java");
            //IFile cFile = project.getProject().getFolder("boot").getFolder("c").getFile("SameName.java");
            //IFile dFile = project.getProject().getFolder("specs").getFolder("d").getFile("SameName.java");
            List<IFile> expectedResources = new LinkedList<IFile>();
            expectedResources.add(mainFile);
            expectedResources.add(mainFile);
            expectedResources.add(defaultFile);
            expectedResources.add(defaultFile);
            expectedResources.add(defaultFile);
            expectedResources.add(mainFile);
            expectedResources.add(aFile);
            expectedResources.add(aFile);
            expectedResources.add(aFile);
            expectedResources.add(mainFile);
            expectedResources.add(aSubFile);
            expectedResources.add(aSubFile);
            expectedResources.add(aSubFile);
            expectedResources.add(mainFile);
            expectedResources.add(bFile);
            expectedResources.add(bFile);
            expectedResources.add(bFile);
            expectedResources.add(mainFile);
            //expectedResources.add(cFile); // API files are not included in symbolic execution tree.
            //expectedResources.add(cFile); // API files are not included in symbolic execution tree.
            //expectedResources.add(cFile); // API files are not included in symbolic execution tree.
            expectedResources.add(mainFile);
            //expectedResources.add(dFile); // API files are not included in symbolic execution tree.
            expectedResources.add(mainFile);
            expectedResources.add(mainFile);
            // Configure method contract usage
            SWTBotView symbolicSettingsView = bot.viewById(SymbolicExecutionSettingsView.VIEW_ID);
            TestUtilsUtil.clickDirectly(symbolicSettingsView.bot().radio(SymbolicExecutionStrategy.Factory.METHOD_TREATMENT_CONTRACT));
            // Get debug target TreeItem
            SWTBotTreeItem launchTreeItem = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select first thread
            // Resume execution
            resume(bot, launchTreeItem, target);
            // Make sure that correct source resources are computed for each IStackFrame
            Iterator<IFile> expectedIter = expectedResources.iterator();
            SEDPreorderIterator iterator = new SEDPreorderIterator(target);
            while (iterator.hasNext()) {
               ISEDDebugElement next = iterator.next();
               if (next instanceof IStackFrame) {
                  Object source = launch.getSourceLocator().getSourceElement((IStackFrame)next);
                  IFile expected = expectedIter.next();
                  assertEquals(source, expected);
               }
            }
            assertFalse(iterator.hasNext());
            assertFalse(expectedIter.hasNext());
         }
      };
      doKeYDebugTargetTest("SWTBotKeYSourceLookupParticipantTest_testResourceFindingWithSameNames",
                           Activator.PLUGIN_ID,
                           "data/sameNamesSourceLocationTest/src",
                           configurator,
                           true,
                           true,
                           createMethodSelector("Main", "main"), 
                           null,
                           null,
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
}