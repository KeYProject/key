package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.wizard.SearchWizard;

/**
 * This action opens the {@link SearchWizard}.
 * @author Martin Hentschel
 */
public class SearchAnnotationAction implements ISEDAnnotationAction {
   /**
    * {@inheritDoc}
    */
   @Override
   public void run(Shell shell, ISEDDebugTarget target) {
      SearchWizard.openWizard(shell, target);
   }
}
