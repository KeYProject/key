package org.key_project.sed.ui.wizard;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.annotation.impl.CommentAnnotationLink;
import org.key_project.sed.ui.wizard.page.CommentWizardPage;

/**
 * The edit comment {@link Wizard} which edits a {@link CommentAnnotationLink}s.
 * @author Martin Hentschel
 */
public class EditCommentWizard extends Wizard {
   /**
    * The {@link CommentAnnotationLink} to edit.
    */
   private final CommentAnnotationLink link;
   
   /**
    * The shown {@link CommentWizardPage}.
    */
   private CommentWizardPage commentWizardPage;

   /**
    * Constructor.
    * @param link The {@link CommentAnnotationLink} to edit.
    */
   public EditCommentWizard(CommentAnnotationLink link) {
      Assert.isNotNull(link);
      this.link = link;
      setWindowTitle("Edit Comment");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      commentWizardPage = new CommentWizardPage("commentWizardPage", "Edit " + link.getSource() + " Comment", "Define comment.", link.getComment());
      addPage(commentWizardPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      link.setComment(commentWizardPage.getComment());
      return true;
   }
   
   /**
    * Opens the {@link EditCommentWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param link The {@link CommentAnnotationLink} to edit.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, CommentAnnotationLink link) {
      WizardDialog dialog = new WizardDialog(parentShell, new EditCommentWizard(link));
      return dialog.open();
   }
}
