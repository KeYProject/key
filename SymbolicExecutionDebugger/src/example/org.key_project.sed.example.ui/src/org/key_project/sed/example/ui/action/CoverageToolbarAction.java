package org.key_project.sed.example.ui.action;

import org.eclipse.debug.ui.actions.AbstractLaunchToolbarAction;
import org.key_project.sed.example.ui.util.ExampleLaunchUtil;

/**
 * The action for the "SED Examples" mode in the toolbar.
 * @author Martin Hentschel
 */
public class CoverageToolbarAction extends AbstractLaunchToolbarAction {
   /**
    * Constructor.
    */
   public CoverageToolbarAction() {
      super(ExampleLaunchUtil.SED_EXAMPLES_LAUNCH_GROUP_ID);
   }
}