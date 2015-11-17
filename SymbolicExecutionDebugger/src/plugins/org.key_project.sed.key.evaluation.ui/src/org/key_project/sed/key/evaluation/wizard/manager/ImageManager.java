package org.key_project.sed.key.evaluation.wizard.manager;

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.ImageQuestion;

public class ImageManager extends AbstractQuestionInputManager {
   private Label label;
   
   private Image image;
   
   public ImageManager(FormToolkit toolkit, 
                       Composite parent, 
                       ImageQuestion question) {
      label = toolkit.createLabel(parent, null, SWT.WRAP);
      if (question.getImageData() != null) {
         image = new Image(parent.getDisplay(), question.getImageData());
      }
      label.setImage(image);
      if (parent.getLayout() instanceof GridLayout) {
         label.setLayoutData(new GridData(GridData.CENTER, GridData.CENTER, true, true));
      }
   }

   @Override
   public void dispose() {
      if (image != null) {
         image.dispose();
      }
   }

   @Override
   protected void enableControls(boolean enabled) {
      label.setEnabled(enabled);
   }

   @Override
   public Control getFocusControl() {
      return label;
   }
}
