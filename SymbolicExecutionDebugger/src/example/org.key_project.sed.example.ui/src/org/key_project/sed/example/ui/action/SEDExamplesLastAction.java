package org.key_project.sed.example.ui.action;

import org.eclipse.debug.ui.actions.RelaunchLastAction;
import org.key_project.sed.example.ui.util.ExampleLaunchUtil;

/**
 * The action to re-launch the last launch in "SED Examples" mode.
 * @author Martin Hentschel
 */
public class SEDExamplesLastAction extends RelaunchLastAction {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getMode() {
      return ExampleLaunchUtil.SED_EXAMPLES_MODE;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getLaunchGroupId() {
      return ExampleLaunchUtil.SED_EXAMPLES_LAUNCH_GROUP_ID;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getText() {
      return "SED Example Last Launched";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getTooltipText() {
      return "SED Example Last Launched";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getDescription() {
      return "SED Example Last Launched";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getCommandId() {
      return "org.key_project.sed.example.ui.commands.launchLastCommand";
   }
}