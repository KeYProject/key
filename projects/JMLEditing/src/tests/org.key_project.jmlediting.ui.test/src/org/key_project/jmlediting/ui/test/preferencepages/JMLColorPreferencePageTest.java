package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.help.ui.internal.ExecuteCommandAction;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.ui.preferencepages.JMLColorPreferencePage;
import org.key_project.jmlediting.ui.test.TestUtils;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;

/**
 * Testingplan:
 * <ul>
 * <li>First test, whether the color shown in the ColorSelector is the color
 * from JMLSettings</li>
 * <li>Test setting a new JML Color and check the Method other use to get the
 * JMLColor</li>
 * <li>Test afterwards the RestoreDefault Button and check again</li>
 * <li>At last test whether a new opening of the Preferences still show the
 * right color.</li>
 * </ul>
 *
 * @author Thomas Glaser
 *
 */
public class JMLColorPreferencePageTest {
   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private SWTBotButton commentColorButton;

   @BeforeClass
   public static void init() {
      TestUtils.prepareWorkbench(bot);
   }

   @Before
   public void openGlobalJMLColorSettings() {
      // We need to do something special on mac
      if (System.getProperty("os.name").toLowerCase().contains("mac")) {
         // Cannot access the menu item for preferences on mac because it is
         // located in a native menu, which even prohibits the key shortcut to
         // work using SWT bot.
         // Therefore, I use the following action to open the preferences window
         // which makes use of nun public UI
         // I took the code from here, where the same problem was solved:
         // https://code.google.com/p/swordfish-tooling/source/diff?spec=svn843&r=843&format=side&path=/trunk/org.eclipse.swordfish.tooling.systemtest/src/org/eclipse/swordfish/tooling/target/platform/test/ide/MacEclipseIDE.java
         // This code needs the dependency on help.ui
         final Thread t = new Thread() {
            @SuppressWarnings("restriction")
            @Override
            public void run() {
               final ExecuteCommandAction action = new ExecuteCommandAction();
               action.setInitializationString("org.eclipse.ui.window.preferences");
               action.run();
            }
         };
         t.start();
      }
      else {
         // On windows and other linux/unix implementations beside mac this
         // command should work
         bot.menu("Window").menu("Preferences").click();
      }
      bot.sleep(100);
      this.navigateToJMLColorSettings();
      this.setCommentColorButton();
   }

   /*
    * needed for setting the Color
    */
   private void setCommentColorButton() {
      this.commentColorButton = bot.buttonWithId(
            JMLColorPreferencePage.TEST_KEY, "CommentColor");
   }

   private void navigateToJMLColorSettings() {
      bot.tree().getTreeItem("JML").select().expand().getNode("Color").select();
   }

   /*
    * hack needed, because native Dialogs can't be testet with SWTBot
    */
   private void setColor(final RGB commentColor) {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            final Object oSelector = JMLColorPreferencePageTest.this.commentColorButton.widget
                  .getData();
            assertTrue(oSelector instanceof ColorSelector);
            final ColorSelector selector = (ColorSelector) oSelector;
            selector.setColorValue(commentColor);
         }
      });
   }

   /*
    * hack needed, because native Dialogs can't be testet with SWTBot
    */
   private void checkColor(final RGB colorToCheck) {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            final Object oSelector = JMLColorPreferencePageTest.this.commentColorButton.widget
                  .getData();
            assertTrue(oSelector instanceof ColorSelector);
            final ColorSelector selector = (ColorSelector) oSelector;
            assertEquals("ColorSelector doesn't show the right color",
                  colorToCheck, selector.getColorValue());
         }
      });
   }

   /*
    * execute Testingplan
    */
   @Test
   public void testColorSettings() {
      // first check whether the ColorSelector shows the right color at the
      // beginning.
      this.checkColor(JMLUiPreferencesHelper.getWorkspaceJMLColor());

      RGB testColor = new RGB(255, 0, 0);
      this.setColor(testColor);
      bot.button("Apply").click();
      assertEquals("Not the right JML-Color was set.", testColor,
            JMLUiPreferencesHelper.getWorkspaceJMLColor());
      bot.button("Restore Defaults").click();
      bot.button("OK").click();
      assertEquals("Restore Default JML Color did not work.",
            JMLUiPreferencesHelper.getDefaultJMLColor(),
            JMLUiPreferencesHelper.getWorkspaceJMLColor());

      // final test
      testColor = new RGB(0, 255, 0);
      this.setColor(testColor);
      bot.button("OK").click();
      bot.sleep(100);
      this.openGlobalJMLColorSettings();
      this.checkColor(JMLUiPreferencesHelper.getWorkspaceJMLColor());
      this.checkColor(testColor);
   }
}
