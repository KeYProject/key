package org.key_project.sed.key.evaluation.wizard.manager;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.LabelQuestion;

public class LabelManager extends AbstractQuestionInputManager {
   private Label label;
   
   public LabelManager(FormToolkit toolkit, 
                       Composite parent, 
                       LabelQuestion question) {
      label = toolkit.createLabel(parent, question.getText());
   }

   @Override
   public void dispose() {
      // Nothing special to do
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
