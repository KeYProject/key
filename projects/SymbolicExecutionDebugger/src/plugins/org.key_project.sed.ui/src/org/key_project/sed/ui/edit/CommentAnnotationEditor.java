package org.key_project.sed.ui.edit;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.sed.core.annotation.impl.CommentAnnotation;
import org.key_project.util.java.StringUtil;

/**
 * An {@link ISEDAnnotationEditor} to edit {@link CommentAnnotation}s.
 * @author Martin Hentschel
 */
public class CommentAnnotationEditor extends AbstractSEDAnnotationEditor {
   /**
    * Defines the comment type.
    */
   private Text commentTypeText;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Control createContent(Composite parent) {
      Group searchGroup = new Group(parent, SWT.NONE);
      searchGroup.setText("Comment");
      searchGroup.setLayout(new GridLayout(2, false));
      Label searchLabel = new Label(searchGroup, SWT.NONE);
      searchLabel.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));
      searchLabel.setText("&Type");
      commentTypeText = new Text(searchGroup, SWT.BORDER | SWT.MULTI);
      commentTypeText.setLayoutData(new GridData(GridData.FILL_BOTH));
      Assert.isTrue(getAnnotation() instanceof CommentAnnotation);
      commentTypeText.setText(((CommentAnnotation)getAnnotation()).getCommentType());
      commentTypeText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updateErrorMessage();
         }
      });
      return searchGroup;
   }

   /**
    * Updates the shown error message.
    */
   protected void updateErrorMessage() {
      boolean valid = !StringUtil.isTrimmedEmpty(commentTypeText.getText());
      setErrorMessage(valid ? null : "No type defined.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void applyChanges(IProgressMonitor monitor) throws Exception {
      CommentAnnotation annotation = (CommentAnnotation)getAnnotation();
      annotation.setCommentType(commentTypeText.getText());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean needsProgressMonitor() {
      return false;
   }
}
