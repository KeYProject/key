package org.key_project.jmlediting.ui.test;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable;
import org.eclipse.swtbot.swt.finder.results.BoolResult;
import org.eclipse.swtbot.swt.finder.utils.internal.Assert;
import org.eclipse.swtbot.swt.finder.waits.DefaultCondition;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;

public class ShellIsActiveWithEmptyText extends DefaultCondition {

   private final String text;

   public ShellIsActiveWithEmptyText(final String text) {
      Assert.isNotNull(text, "The shell text was null"); //$NON-NLS-1$
      this.text = text;
   }

   @Override
   public String getFailureMessage() {
      return "The shell '" + this.text + "' did not activate"; //$NON-NLS-1$ //$NON-NLS-2$
   }

   @Override
   public boolean test() throws Exception {
      try {
         final SWTBotShell shell = this.bot.shell(this.text);
         return UIThreadRunnable.syncExec(new BoolResult() {
            @Override
            public Boolean run() {
               return shell.widget.isVisible() || shell.widget.isFocusControl();
            }
         });
      }
      catch (final WidgetNotFoundException e) {
      }
      return false;
   }

}
