package org.key_project.sed.ui.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.impl.CommentAnnotation;
import org.key_project.util.java.StringUtil;

/**
 * This {@link WizardPage} defines a comment.
 * @author Martin Hentschel
 */
public class NewCommentWizardPage extends CommentWizardPage {
   /**
    * All available comment annotations.
    */
   private final ISEDAnnotation[] commentAnnotations;
   
   /**
    * Defines the comment type.
    */
   private Combo commentTypeCombo;
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param title The title to show.
    * @param description The description to show.
    */
   public NewCommentWizardPage(String pageName, String title, String description, String initialComment, ISEDAnnotation[] commentAnnotations) {
      super(pageName, title, description, initialComment);
      this.commentAnnotations = commentAnnotations;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void addInitialContent(Composite parent) {
      Label typeLabel = new Label(parent, SWT.NONE);
      typeLabel.setText("&Type");
      commentTypeCombo = new Combo(parent, SWT.NONE);
      String initialText = null;
      if (commentAnnotations != null) {
         for (ISEDAnnotation annotation : commentAnnotations) {
            if (annotation instanceof CommentAnnotation) {
               String type = ((CommentAnnotation) annotation).getCommentType();
               if (initialText == null) {
                  initialText = type;
               }
               commentTypeCombo.add(type);
            }
         }
      }
      commentTypeCombo.setText(initialText != null ? initialText : CommentAnnotation.DEFAULT_COMMENT_TYPE);
      commentTypeCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      commentTypeCombo.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageComplete();
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void updatePageComplete() {
      if (StringUtil.isTrimmedEmpty(getCommentType())) {
         setPageComplete(false);
         setErrorMessage("No type defined.");
      }
      else {
         super.updatePageComplete();
      }
   }
   
   /**
    * Returns the defined comment type.
    * @return The defined comment type.
    */
   public String getCommentType() {
      return commentTypeCombo.getText();
   }
}
