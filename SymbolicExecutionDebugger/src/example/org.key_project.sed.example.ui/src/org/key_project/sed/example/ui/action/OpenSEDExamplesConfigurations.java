package org.key_project.sed.example.ui.action;

import org.eclipse.debug.ui.actions.OpenLaunchDialogAction;
import org.key_project.sed.example.ui.util.ExampleLaunchUtil;

/**
 * The action to open the "SED Examples" launch configuration.
 */
public class OpenSEDExamplesConfigurations extends OpenLaunchDialogAction {
   /**
    * Constructor.
    */
   public OpenSEDExamplesConfigurations() {
      super(ExampleLaunchUtil.SED_EXAMPLES_LAUNCH_GROUP_ID);
   }
}