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
import org.key_project.sed.ui.wizard.page.NewCommentWizardPage;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

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
    * The {@link ISEDAnnotationType} for comments.
    */
   private final ISEDAnnotationType annotationType;
   
   /**
    * All available comment annotations.
    */
   private final ISEDAnnotation[] commentAnnotations;
   
   /**
    * The shown {@link NewCommentWizardPage}.
    */
   private NewCommentWizardPage newCommentWizardPage;

   /**
    * Constructor.
    * @param node The {@link ISEDDebugTarget} to search in.
    */
   public NewCommentWizard(ISEDDebugNode node) {
      this.node = node;
      this.annotationType = SEDAnnotationUtil.getAnnotationtype(CommentAnnotationType.TYPE_ID);
      this.commentAnnotations = node.getDebugTarget().getRegisteredAnnotations(annotationType);
      Assert.isNotNull(node);
      Assert.isNotNull(annotationType);
      setWindowTitle("New Comment");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      newCommentWizardPage = new NewCommentWizardPage("newCommentWizardPage", "New Comment", "Define comment.", null, commentAnnotations);
      addPage(newCommentWizardPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      ISEDDebugTarget target = node.getDebugTarget();
      final String commentType = newCommentWizardPage.getCommentType();
      ISEDAnnotation annotation = ArrayUtil.search(commentAnnotations, new IFilter<ISEDAnnotation>() {
         @Override
         public boolean select(ISEDAnnotation element) {
            return element instanceof CommentAnnotation &&
                   ObjectUtil.equals(commentType, ((CommentAnnotation)element).getCommentType());
         }
      });
      if (annotation == null) {
         annotation = annotationType.createAnnotation();
         ((CommentAnnotation)annotation).setCommentType(commentType);
         target.registerAnnotation(annotation);
      }
      CommentAnnotationLink link = (CommentAnnotationLink)annotationType.createLink(annotation, node);
      link.setComment(newCommentWizardPage.getComment());
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
