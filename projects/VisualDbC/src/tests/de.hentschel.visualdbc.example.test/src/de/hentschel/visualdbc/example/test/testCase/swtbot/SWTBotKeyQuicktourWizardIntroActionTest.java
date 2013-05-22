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

package de.hentschel.visualdbc.example.test.testCase.swtbot;

import java.util.Properties;

import junit.framework.TestCase;

import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.ui.internal.intro.impl.IntroPlugin;
import org.junit.Test;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.example.action.KeyQuicktourWizardIntroAction;

/**
 * SWT Bot tests for {@link KeyQuicktourWizardIntroAction}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SWTBotKeyQuicktourWizardIntroActionTest extends TestCase {
   /**
    * Tests the action execution.
    */
   @Test
   public void testExecution() {
      // Open intro
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.menuClick(bot, "Help", "Welcome");
      // Execute command
      Display.getDefault().asyncExec(new Runnable() {
         @Override
         public void run() {
            KeyQuicktourWizardIntroAction action = new KeyQuicktourWizardIntroAction();
            action.run(IntroPlugin.getIntro().getIntroSite(), new Properties());
         }
      });
      // Get opened wizard dialog and close it
      SWTBotShell shell = bot.shell("New Java Project with content from KeY Quicktour");
      shell.close();
   }
}