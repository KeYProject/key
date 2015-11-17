package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.ui.wizard.SearchWizard;

/**
 * This action opens the {@link SearchWizard}.
 * @author Martin Hentschel
 */
public class SearchAnnotationAction implements ISEAnnotationAction {
   /**
    * {@inheritDoc}
    */
   @Override
   public void run(Shell shell, ISEDebugTarget target) {
      SearchWizard.openWizard(shell, target);
   }
}
