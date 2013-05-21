package org.key_project.sed.key.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.sed.key.ui.visualization.execution_tree.command.VisualizeConfigurationsCommand;

/**
 * This {@link PropertyTester} can be used to check if configurations can
 * be visualized for the given {@link Object}. The check is delegated to
 * {@link VisualizeConfigurationsCommand#canVisualize(Object)}.
 * @author Martin Hentschel
 */
public class CanVisualizeConfigurationsPropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      try {
         return VisualizeConfigurationsCommand.canVisualize(receiver);
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }
}
