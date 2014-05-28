package org.key_project.sed.ui.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.util.java.StringUtil;

/**
 * This {@link WizardPage} defines a comment.
 * @author Martin Hentschel
 */
public class CommentWizardPage extends WizardPage {
   /**
    * The initial comment to show.
    */
   private final String initialComment;
   
   /**
    * Defines the comment.
    */
   private Text commentText;
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param title The title to show.
    * @param description The description to show.
    */
   public CommentWizardPage(String pageName, String title, String description, String initialComment) {
      super(pageName);
      this.initialComment = initialComment;
      setTitle(title);
      setDescription(description);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      setControl(root);
      root.setLayout(new GridLayout(2, false));
      addInitialContent(root);
      Label commentLabel = new Label(root, SWT.NONE);
      commentLabel.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));
      commentLabel.setText("&Comment");
      commentText = new Text(root, SWT.BORDER | SWT.MULTI);
      if (initialComment != null) {
         commentText.setText(initialComment);
      }
      commentText.setLayoutData(new GridData(GridData.FILL_BOTH));
      commentText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageComplete();
         }
      });
      updatePageComplete();
   }

   /**
    * Adds some optional initial content.
    * @param composite The {@link Composite} to publish.
    */
   protected void addInitialContent(Composite parent) {
   }
   
   /**
    * Updates the page complete state.
    */
   protected void updatePageComplete() {
      if (StringUtil.isTrimmedEmpty(getComment())) {
         setPageComplete(false);
         setErrorMessage("No comment defined.");
      }
      else {
         setPageComplete(true);
         setErrorMessage(null);
      }
   }
   
   /**
    * Returns the defined comment.
    * @return The defined comment.
    */
   public String getComment() {
      return commentText.getText();
   }
}
