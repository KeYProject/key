package org.key_project.util.test.util;

import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.swt.finder.results.BoolResult;
import org.eclipse.swtbot.swt.finder.results.IntResult;
import org.eclipse.swtbot.swt.finder.widgets.AbstractSWTBotControl;
import org.key_project.util.eclipse.swt.CustomProgressBar;

/**
 * This represents a {@link CustomProgressBar} widget.
 * @author Martin Hentschel
 */
public class SWTBotCustomProgressBar extends AbstractSWTBotControl<CustomProgressBar> {
   /**
    * Constructor.
    * @param w the widget.
    * @throws WidgetNotFoundException if the widget is <code>null</code> or widget has been disposed.
    */
   public SWTBotCustomProgressBar(CustomProgressBar w) throws WidgetNotFoundException {
      super(w);
   }
   
   /**
    * Factory method.
    * @param bot The {@link SWTBot} to use.
    * @param index The index in the list of all found {@link CustomProgressBar}s.
    * @return The instantiated {@link SWTBotCustomProgressBar}.
    * @throws WidgetNotFoundException If no widget is available.
    */
   public static SWTBotCustomProgressBar customProgressBar(SWTBot bot, int index) throws WidgetNotFoundException {
      CustomProgressBar w = (CustomProgressBar)bot.widget(WidgetMatcherFactory.widgetOfType(CustomProgressBar.class), index);
      if (w != null) {
         return new SWTBotCustomProgressBar(w);
      }
      else{
         throw new WidgetNotFoundException("Can't find CustomProgressBar.");
      }
   }
   
   /**
    * Queries {@link CustomProgressBar#hasErrors()}.
    * @return The result value.
    */
   public boolean hasErrors() {
      return syncExec(new BoolResult() {
         @Override
         public Boolean run() {
            return widget.hasErrors();
         }
      });
   }
   
   /**
    * Queries {@link CustomProgressBar#isStopped()}.
    * @return The result value.
    */
   public boolean isStopped() {
      return syncExec(new BoolResult() {
         @Override
         public Boolean run() {
            return widget.isStopped();
         }
      });
   }
   
   /**
    * Queries {@link CustomProgressBar#getTicksDone()}.
    * @return The result value.
    */
   public int getTicksDone() {
      return syncExec(new IntResult() {
         @Override
         public Integer run() {
            return widget.getTicksDone();
         }
      });
   }
   
   /**
    * Queries {@link CustomProgressBar#getMaximum()}.
    * @return The result value.
    */
   public int getMaximum() {
      return syncExec(new IntResult() {
         @Override
         public Integer run() {
            return widget.getMaximum();
         }
      });
   }
}
