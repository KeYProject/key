package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.ui.preferencepages.JMLColorPropertyPreferencePage;
import org.key_project.jmlediting.ui.test.TestUtils;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;

/**
 * Testingplan:
 * <ul>
 * <li>Test setting a new JML Color and check the Method other use to get the
 * JMLColor</li>
 * <li>Test afterward the RestoreDefault Button and check again</li>
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
      bot.menu("Window").menu("Preferences").click();
      bot.sleep(100);
      this.navigateToJMLColorSettings();
      this.setCommentColorButton();
   }

   /*
    * needed for setting the Color
    */
   private void setCommentColorButton() {
      this.commentColorButton = bot.buttonWithId(
            JMLColorPropertyPreferencePage.TEST_KEY, "CommentColor");
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
    * execute Testingplan
    */
   @Test
   public void testColorSettings() {
      final RGB testColor = new RGB(255, 0, 0);
      this.setColor(testColor);
      bot.button("Apply").click();
      assertEquals(testColor, JMLUiPreferencesHelper.getWorkspaceJMLColor());
      bot.button("Restore Defaults").click();
      bot.button("OK").click();
      assertEquals(JMLUiPreferencesHelper.getDefaultJMLColor(),
            JMLUiPreferencesHelper.getWorkspaceJMLColor());
   }
}
