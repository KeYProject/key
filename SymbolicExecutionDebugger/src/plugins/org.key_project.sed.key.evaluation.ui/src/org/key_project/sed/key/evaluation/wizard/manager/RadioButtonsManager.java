package org.key_project.sed.key.evaluation.wizard.manager;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage.ICreateControlCallback;
import org.key_project.util.java.ObjectUtil;

public class RadioButtonsManager extends AbstractButtonsManager<RadioButtonsQuestion> {
   public RadioButtonsManager(AbstractEvaluationWizardPage<?> wizardPage, FormToolkit toolkit, Composite parent, QuestionInput questionInput, RadioButtonsQuestion question, ICreateControlCallback callback) {
      super(wizardPage, toolkit, parent, questionInput, question, callback);
   }

   @Override
   protected int getButtonStyle() {
      return SWT.RADIO;
   }

   @Override
   protected boolean isChoiceSelected(String inputValue, String choiceValue) {
      return ObjectUtil.equals(inputValue, choiceValue);
   }

   @Override
   protected void handleButtonSelected(QuestionInput questionInput, Button button, Choice choice) {
      if (button.getSelection()) {
         questionInput.setValue(choice.getValue());
         updateValueSetAt(questionInput);
         updateChoiceChildrenEnabled();
      }
   }
}