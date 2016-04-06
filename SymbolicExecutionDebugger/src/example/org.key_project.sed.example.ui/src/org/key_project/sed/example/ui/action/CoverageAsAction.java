package org.key_project.sed.example.ui.action;

import org.eclipse.debug.ui.actions.LaunchShortcutsAction;
import org.key_project.sed.example.ui.util.ExampleLaunchUtil;

/**
 * Implementation of the "SED Examples" menu.
 * @author Martin Hentschel
 */
public class CoverageAsAction extends LaunchShortcutsAction {
   /**
    * Constructor.
    */
   public CoverageAsAction() {
      super(ExampleLaunchUtil.SED_EXAMPLES_LAUNCH_GROUP_ID);
   }
}