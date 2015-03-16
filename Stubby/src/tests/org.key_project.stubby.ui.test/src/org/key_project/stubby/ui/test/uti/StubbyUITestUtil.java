package org.key_project.stubby.ui.test.uti;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public final class StubbyUITestUtil {
   /**
    * Forbid instances by this private constructor.
    */
   private StubbyUITestUtil() {
   }
   
   /**
    * Selects the project explorer view and the defined path.
    * @param bot The {@link SWTBotTree} to find the package explorer view.
    * @param toSelects The path to select.
    * @return The selected element.
    */
   public static SWTBotTreeItem selectInProjectExplorer(SWTWorkbenchBot bot, String... toSelects) {
      SWTBotView viewBot = getProjectExplorer(bot);
      return selectInTree(viewBot.bot().tree(), toSelects);
   }

   /**
    * Returns the project explorer view or its JDT version package explorer.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @return The found {@link SWTBotView}.
    */
   public static SWTBotView getProjectExplorer(SWTWorkbenchBot bot) {
      SWTBotView viewBot = null;
      try {
         viewBot = bot.viewByTitle("Package Explorer");
         viewBot.show();
      }
      catch (WidgetNotFoundException e) {
         viewBot = bot.viewByTitle("Project Explorer");
         viewBot.show();
      }
      return viewBot;
   }

   /**
    * Selects the element path in the tree.
    * @param treeBot The {@link SWTBotTree} to select in.
    * @param toSelects The path to select.
    * @return The selected element.
    */
   public static SWTBotTreeItem selectInTree(SWTBotTree treeBot, String... toSelects) {
      SWTBotTreeItem lastItem = null;
      for (String segment : toSelects) {
         if (lastItem == null) {
            lastItem = treeBot.getTreeItem(segment);
            if (!lastItem.isExpanded()) {
               lastItem.expand();
            }
         }
         else {
            lastItem = lastItem.getNode(segment);
            if (!lastItem.isExpanded()) {
               lastItem.expand();
            }
         }
      }
      treeBot.select(lastItem);
      return lastItem;
   }
}
