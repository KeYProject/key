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

package org.key_project.key4eclipse.resources.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.Test;
import org.key_project.key4eclipse.resources.ui.test.util.KeY4EclipseResourcesUiTestUtil;
import org.key_project.key4eclipse.resources.ui.wizard.KeYProjectWizard;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link KeYProjectWizard}. 
 * @author Stefan Käsdorf
 */
public class SWTBotKeYProjectWizardTest extends TestCase{
   
   private SWTWorkbenchBot bot;
   
   
   /**
    * Creates a KeYProject by using the KeYProjectWizard. Asserts that the KeYNature and KeYBuild were set.
    * @throws CoreException
    * @throws InterruptedException
    */
   @Test
   public void testKeYProjectWizard() throws CoreException, InterruptedException{
      bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      createKeYProject(bot, "SWTBotKeYProjectWizardTest_testKeYProjectWizard");
      
      IWorkspace workspace = ResourcesPlugin.getWorkspace();
      
      TestUtilsUtil.waitForBuild();
      
      IProject project = workspace.getRoot().getProject("SWTBotKeYProjectWizardTest_testKeYProjectWizard");
      KeY4EclipseResourcesUiTestUtil.assertKeYNature(project);
   }
   
   
   /**
    * Creates a KeYProject by using the KeYProjectWizard.
    * @param bot - the {@link SWTWorkbenchBot} to use
    * @param name - the projects name.
    */
   public static void createKeYProject(SWTWorkbenchBot bot, String name){
      bot.menu("File").menu("New").menu("Project...").click();
      
      SWTBotShell wizardShell = bot.shell("New Project");
      bot.tree().expandNode("KeY").select("KeY Project");
      TestUtilsUtil.clickDirectly(bot.button("Next >"));
 
      wizardShell.bot().textWithLabel("Project name:").setText(name);
 
      bot.button("Finish").click();
      bot.waitUntil(Conditions.shellCloses(wizardShell));
      
   }
   
   
   
}