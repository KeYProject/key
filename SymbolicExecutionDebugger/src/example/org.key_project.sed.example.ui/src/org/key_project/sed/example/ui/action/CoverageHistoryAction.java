package org.key_project.sed.example.ui.action;

import org.eclipse.debug.ui.actions.AbstractLaunchHistoryAction;
import org.key_project.sed.example.ui.util.ExampleLaunchUtil;

/**
 * The history pull-down menu for recent "SED Examples" launches.
 * @author Martin Hentschel
 */
public class CoverageHistoryAction extends AbstractLaunchHistoryAction {
   /**
    * Constructor.
    */
   public CoverageHistoryAction() {
      super(ExampleLaunchUtil.SED_EXAMPLES_LAUNCH_GROUP_ID);
   }
}