package org.key_project.sed.key.evaluation.wizard.manager;

import java.beans.PropertyChangeEvent;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.TextQuestion;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;

public class TextManager extends AbstractEditableQuestionInputManager {
   private final Text text;
   
   public TextManager(AbstractEvaluationWizardPage<?> wizardPage,
                      FormToolkit toolkit, 
                      Composite parent, 
                      QuestionInput questionInput,
                      TextQuestion question) {
      super(wizardPage, questionInput);
      Composite composite = toolkit.createComposite(parent);
      composite.setLayoutData(new GridData(GridData.FILL_BOTH));
      composite.setLayout(new GridLayout(1, false));
      createSection(toolkit, composite, question);
      text = toolkit.createText(composite, questionInput.getValue(), SWT.MULTI | SWT.V_SCROLL);
      text.setLayoutData(new GridData(GridData.FILL_BOTH));
      text.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            handleTextChanged(e);
         }
      });
   }

   protected void handleTextChanged(ModifyEvent e) {
      if (!ObjectUtil.equals(getQuestionInput().getValue(), text.getText())) {
         getQuestionInput().setValue(text.getText());
      }
   }

   @Override
   protected void handleQuestionValueChanged(PropertyChangeEvent evt) {
      if (!ObjectUtil.equals(getQuestionInput().getValue(), text.getText())) {
         SWTUtil.setText(text, getQuestionInput().getValue());
      }
   }

   @Override
   protected void enableControls(boolean enabled) {
      text.setEnabled(enabled);
   }

   @Override
   public Control getFocusControl() {
      return text;
   }
}
