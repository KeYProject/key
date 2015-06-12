package org.key_project.sed.key.evaluation.wizard.manager;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.key_project.sed.key.evaluation.model.definition.LabelQuestion;

public class LabelManager extends AbstractQuestionInputManager {
   private Label label;
   
   public LabelManager(FormToolkit toolkit, 
                       Composite parent, 
                       LabelQuestion question) {
      Composite composite = toolkit.createComposite(parent);
      composite.setLayout(new TableWrapLayout());
      label = toolkit.createLabel(composite, question.getText(), SWT.WRAP);
      label.setLayoutData(new TableWrapData());
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
