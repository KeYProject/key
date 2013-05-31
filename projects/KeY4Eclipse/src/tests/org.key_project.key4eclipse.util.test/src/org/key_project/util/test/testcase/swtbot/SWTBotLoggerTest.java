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

package org.key_project.util.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.Test;
import org.key_project.util.eclipse.Logger;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWT Bot tests for {@link Logger}. 
 * @author Martin Hentschel
 */
public class SWTBotLoggerTest extends TestCase {
   /**
    * Tests {@link Logger#openErrorDialog(Shell, Throwable)}
    */
   @Test
   public void testOpenErrorDialog() {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Close welcome perspective
      TestUtilsUtil.closeWelcomeView(bot);
      // Open error dialog
      OpenErrorDialogRunnable run = new OpenErrorDialogRunnable();
      Display.getDefault().asyncExec(run);
      // Get bot for error shell
      SWTBotShell botShell = bot.shell("Error");
      // Check message label
      assertEquals("My message.", botShell.bot().label(1).getText());
      // Expand details
      botShell.bot().button("Details >>").click();
      // Check list entries
      String[] items = botShell.bot().list().getItems();
      assertEquals(1, items.length);
      assertEquals("My message.", items[0]);
      // Close error shell
      botShell.bot().button("OK").click();
      // Check run result
      assertEquals(IStatus.OK, run.getResult());
   }
   
   /**
    * Runnable to execute {@link Logger#openErrorDialog(Shell, Throwable)}.
    * @author Martin Hentschel
    */
   private static class OpenErrorDialogRunnable implements Runnable {
      /**
       * The dialog result.
       */
      private int result;

      /**
       * {@inheritDoc}
       */
      @Override
      public void run() {
         boolean oldAutomatedMode = ErrorDialog.AUTOMATED_MODE;
         try {
            Shell shell = WorkbenchUtil.getActiveShell();
            ErrorDialog.AUTOMATED_MODE = false;
            result = TestUtilsUtil.createLogger().openErrorDialog(shell, new Exception("My message."));
         }
         finally {
            ErrorDialog.AUTOMATED_MODE = oldAutomatedMode;
         }
      }

      /**
       * Returns the dialog result.
       * @return The dialog result.
       */
      public int getResult() {
         return result;
      }
   }
}