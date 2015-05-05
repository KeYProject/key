package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.wizard.NewCommentWizard;

/**
 * This action opens the {@link NewCommentWizard}.
 * @author Martin Hentschel
 */
public class CommentAnnotationLinkAction implements ISEDAnnotationLinkAction {
   /**
    * {@inheritDoc}
    */
   @Override
   public void run(Shell shell, ISEDDebugNode node) {
      NewCommentWizard.openWizard(shell, node);
   }
}
