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

package de.hentschel.visualdbc.example.test.testCase.swtbot;

import java.util.Properties;

import junit.framework.TestCase;

import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.internal.intro.impl.IntroPlugin;
import org.junit.Test;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.example.action.BankingWizardIntroAction;

/**
 * SWT Bot tests for {@link BankingWizardIntroAction}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SWTBotBankingWizardIntroActionTest extends TestCase {
   /**
    * Tests the action execution.
    */
   @Test
   public void testExecution() {
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      try {
         // Open intro
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot); // Close welcome view required for standalone execution
         TestUtilsUtil.menuClick(bot, "Help", "Welcome");
         // Execute command
         Display.getDefault().asyncExec(new Runnable() {
            @Override
            public void run() {
               BankingWizardIntroAction action = new BankingWizardIntroAction();
               action.run(IntroPlugin.getIntro().getIntroSite(), new Properties());
            }
         });
         // Get opened wizard dialog and close it
         SWTBotShell shell = bot.shell("New Java Project with content from Banking Example");
         shell.close();
      }
      finally {
         // Restore perspective
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }
}