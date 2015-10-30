package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.impl.CommentAnnotationLink;
import org.key_project.sed.ui.wizard.EditCommentWizard;

/**
 * Edits a {@link CommentAnnotationLink} via the {@link EditCommentWizard}.
 * @author Martin Hentschel
 */
public class CommentAnnotationLinkEditAction implements ISEAnnotationLinkEditAction {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canEdit(ISEAnnotationLink link) {
      return link instanceof CommentAnnotationLink;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void edit(Shell shell, ISEAnnotationLink link) {
      EditCommentWizard.openWizard(shell, (CommentAnnotationLink)link);
   }
}
