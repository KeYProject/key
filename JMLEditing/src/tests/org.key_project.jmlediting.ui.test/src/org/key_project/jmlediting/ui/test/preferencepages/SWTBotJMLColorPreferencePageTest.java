package org.key_project.jmlediting.ui.test.preferencepages;

import static org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable.syncExec;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.results.Result;
import org.eclipse.swtbot.swt.finder.results.VoidResult;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.ui.preferencepages.JMLColorPreferencePage;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper.ColorProperty;
import org.key_project.util.test.util.TestUtilsUtil;

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
 */
public class SWTBotJMLColorPreferencePageTest {
   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   @BeforeClass
   public static void init() {
      TestUtilsUtil.closeWelcomeView();
   }

   @AfterClass
   public static void resetColor() {
      JMLUiPreferencesHelper.resetToDefault(ColorProperty.COMMENT);
   }

   /*
    * hack needed, because native Dialogs can't be testet with SWTBot
    */
   private void setCommentRGB(final SWTBotButton commentColorButton, final RGB commentColor) {
      syncExec(new VoidResult() {
         @Override
         public void run() {
            final Object oSelector = commentColorButton.widget.getData();
            if (oSelector instanceof ColorSelector) {
               ((ColorSelector) oSelector).setColorValue(commentColor);
            }
         }
      });
   }

   private void checkCommentRGB(SWTBotButton commentColorButton, RGB expectedRGB) {
      RGB actualRGB = getCommentRGB(commentColorButton);
      assertNotNull(actualRGB);
      assertEquals("ColorSelector doesn't show the right color", expectedRGB, actualRGB);
   }
   
   /*
    * hack needed, because native Dialogs can't be testet with SWTBot
    */
   public RGB getCommentRGB(final SWTBotButton commentColorButton) {
      return syncExec(new Result<RGB>() {
         @Override
         public RGB run() {
            final Object oSelector = commentColorButton.widget.getData();
            if (oSelector instanceof ColorSelector) {
               return ((ColorSelector) oSelector).getColorValue();
            }
            else {
               return null;
            }
         }
      });
   }

   /*
    * execute Testingplan
    */
   @Test
   public void testColorSettings() {
      SWTBotShell preferenceShell = JMLEditingUITestUtils.openJMLColorsPreferencePage(bot);
      SWTBotButton commentColorButton = preferenceShell.bot().buttonWithId(JMLColorPreferencePage.TEST_KEY, ColorProperty.COMMENT.getPropertyName());
      
      // first check whether the ColorSelector shows the right color at the beginning.
      this.checkCommentRGB(commentColorButton, JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.COMMENT));

      RGB testColor = new RGB(255, 0, 0);
      this.setCommentRGB(commentColorButton, testColor);
      preferenceShell.bot().button("Apply").click();
      // Need to wait until the UI events has been processed
      assertEquals("Not the right JML-Color was set.", 
                   testColor,
                   JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.COMMENT));
      preferenceShell.bot().button("Restore Defaults").click();
      preferenceShell.bot().button("Apply").click();
      assertEquals("Restore Default JML Color did not work.",
                   ColorProperty.COMMENT.getDefaultColor(),
                   JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.COMMENT));
      // final test
      testColor = new RGB(0, 255, 0);
      this.setCommentRGB(commentColorButton, testColor);
      preferenceShell.bot().button(IDialogConstants.OK_LABEL).click();
      // reopen dialog
      preferenceShell = JMLEditingUITestUtils.openJMLColorsPreferencePage(bot);
      commentColorButton = preferenceShell.bot().buttonWithId(JMLColorPreferencePage.TEST_KEY, ColorProperty.COMMENT.getPropertyName());
      this.checkCommentRGB(commentColorButton, JMLUiPreferencesHelper .getWorkspaceJMLColor(ColorProperty.COMMENT));
      this.checkCommentRGB(commentColorButton, testColor);
      preferenceShell.bot().button(IDialogConstants.OK_LABEL).click();
   }
}
