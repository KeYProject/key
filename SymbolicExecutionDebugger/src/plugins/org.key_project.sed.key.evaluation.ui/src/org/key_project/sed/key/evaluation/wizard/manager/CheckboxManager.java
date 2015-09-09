package org.key_project.sed.key.evaluation.wizard.manager;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.CheckboxQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage.ICreateControlCallback;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.StringUtil;

public class CheckboxManager extends AbstractButtonsManager<CheckboxQuestion> {
   public CheckboxManager(AbstractEvaluationWizardPage<?> wizardPage, FormToolkit toolkit, Composite parent, QuestionInput questionInput, CheckboxQuestion question, ICreateControlCallback callback) {
      super(wizardPage, toolkit, parent, questionInput, question, callback);
   }

   @Override
   protected int getButtonStyle() {
      return SWT.CHECK;
   }

   @Override
   protected boolean isChoiceSelected(String inputValue, String choiceValue) {
      if (!StringUtil.isEmpty(inputValue)) {
         String[] values = inputValue.split(CheckboxQuestion.VALUE_SEPARATOR);
         return ArrayUtil.contains(values, choiceValue);
      }
      else {
         return false;
      }
   }

   @Override
   protected void handleButtonSelected(QuestionInput questionInput, Button button, Choice choice) {
      if (button.getSelection()) {
         String value = questionInput.getValue();
         if (!StringUtil.isEmpty(value)) {
            value += CheckboxQuestion.VALUE_SEPARATOR + choice.getValue();
         }
         else {
            value = choice.getValue();
         }
         questionInput.setValue(value);
         updateValueSetAt(questionInput);
      }
      else {
         String value = questionInput.getValue();
         List<String> valuesList;
         if (!StringUtil.isEmpty(value)) {
            String[] values = value.split(CheckboxQuestion.VALUE_SEPARATOR);
            valuesList = CollectionUtil.toList(values);
            valuesList.remove(choice.getValue());
         }
         else {
            valuesList = new LinkedList<String>();
         }
         questionInput.setValue(valuesList.isEmpty() ? null : CollectionUtil.toString(valuesList, CheckboxQuestion.VALUE_SEPARATOR));
         updateValueSetAt(questionInput);
      }
      updateChoiceChildrenEnabled();
      if (choice.countChildQuestions() >= 1) {
         getWizardPage().reflow();
      }
   }
}