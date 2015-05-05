package org.key_project.sed.key.evaluation.wizard.manager;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.services.IDisposable;
import org.key_project.sed.key.evaluation.model.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.RadioButtonsQuestion.Choice;
import org.key_project.sed.key.evaluation.model_input.QuestionInput;
import org.key_project.util.java.ObjectUtil;

public class RadioButtonsManager implements IDisposable {
   private final QuestionInput questionInput;
   
   private final List<Button> buttons = new LinkedList<Button>();
   
   private final PropertyChangeListener questionListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleQuestionValueChanged(evt);
      }
   };
   
   private Composite composite;
   
   public RadioButtonsManager(final FormToolkit toolkit, 
                              final Composite parent, 
                              final QuestionInput questionInput, 
                              final RadioButtonsQuestion question) {
      questionInput.addPropertyChangeListener(QuestionInput.PROP_VALUE, questionListener);
      this.questionInput = questionInput;
      composite = toolkit.createComposite(parent);
      if (question.getLabel() != null) {
         composite.setLayout(new GridLayout(question.countChoices() + 1, false));
         toolkit.createLabel(composite, question.getLabel());
      }
      else {
         composite.setLayout(new GridLayout(question.countChoices(), false));
      }
      for (final Choice choice : question.getChoices()) {
         final Button button = toolkit.createButton(composite, choice.getText(), SWT.RADIO);
         button.setData(choice.getValue());
         button.setToolTipText(choice.getTooltip());
         if (ObjectUtil.equals(questionInput.getValue(), choice.getValue())) {
            button.setSelection(true);
         }
         button.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
               if (button.getSelection()) {
                  questionInput.setValue(choice.getValue());
               }
            }
         });
         buttons.add(button);
      }
   }

   protected void handleQuestionValueChanged(PropertyChangeEvent evt) {
      for (Button button : buttons) {
         if (ObjectUtil.equals(button.getData(), evt.getNewValue())) {
            button.setSelection(true);
         }
         else {
            button.setSelection(false);
         }
      }
   }
   
   @Override
   public void dispose() {
      questionInput.removePropertyChangeListener(QuestionInput.PROP_VALUE, questionListener);
   }

   public Composite getComposite() {
      return composite;
   }
}