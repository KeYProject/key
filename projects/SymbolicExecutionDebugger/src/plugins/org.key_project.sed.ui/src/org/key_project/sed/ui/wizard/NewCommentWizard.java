package org.key_project.sed.ui.wizard;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.annotation.impl.CommentAnnotation;
import org.key_project.sed.core.annotation.impl.CommentAnnotationLink;
import org.key_project.sed.core.annotation.impl.CommentAnnotationType;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.util.SEDAnnotationUtil;
import org.key_project.sed.ui.wizard.page.CommentWizardPage;

/**
 * The new comment {@link Wizard} which creates a comment via {@link CommentAnnotation}s.
 * @author Martin Hentschel
 */
public class NewCommentWizard extends Wizard {
   /**
    * The {@link ISEDDebugNode} to add a comment to.
    */
   private final ISEDDebugNode node;
   
   /**
    * The shown {@link CommentWizardPage}.
    */
   private CommentWizardPage commentWizardPage;

   /**
    * Constructor.
    * @param node The {@link ISEDDebugTarget} to search in.
    */
   public NewCommentWizard(ISEDDebugNode node) {
      Assert.isNotNull(node);
      this.node = node;
      setWindowTitle("New Comment");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      commentWizardPage = new CommentWizardPage("commentWizardPage", "New Comment", "Define comment.", null);
      addPage(commentWizardPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      ISEDAnnotationType type = SEDAnnotationUtil.getAnnotationtype(CommentAnnotationType.TYPE_ID);
      ISEDDebugTarget target = node.getDebugTarget();
      ISEDAnnotation[] annotations = target.getRegisteredAnnotations(type);
      ISEDAnnotation annotation;
      if (annotations.length >= 1) {
         annotation = annotations[0];
      }
      else {
         annotation = type.createAnnotation();
         target.registerAnnotation(annotation);
      }
      CommentAnnotationLink link = (CommentAnnotationLink)type.createLink(annotation, node);
      link.setComment(commentWizardPage.getComment());
      node.addAnnotationLink(link);
      return true;
   }
   
   /**
    * Opens the {@link NewCommentWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param node The {@link ISEDDebugTarget} to add a new comment to.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, ISEDDebugNode node) {
      WizardDialog dialog = new WizardDialog(parentShell, new NewCommentWizard(node));
      return dialog.open();
   }
}
