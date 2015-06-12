package org.key_project.sed.key.evaluation.wizard.manager;

import java.beans.PropertyChangeEvent;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.jface.fieldassist.ControlDecoration;
import org.eclipse.jface.fieldassist.FieldDecorationRegistry;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.AbstractButtonsQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage.ICreateControlCallback;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

public abstract class AbstractButtonsManager<Q extends AbstractButtonsQuestion> extends AbstractEditableQuestionInputManager {
   private final List<Button> buttons = new LinkedList<Button>();
   private final List<ControlDecoration> buttonDecorations = new LinkedList<ControlDecoration>();
   
   private final Map<Choice, List<IQuestionInputManager>> choiceManagers = new HashMap<Choice, List<IQuestionInputManager>>();
   
   private Composite composite;
   
   public AbstractButtonsManager(AbstractEvaluationWizardPage<?> wizardPage,
                                 FormToolkit toolkit, 
                                 Composite parent, 
                                 QuestionInput questionInput, 
                                 Q question,
                                 ICreateControlCallback callback) {
      super(wizardPage, questionInput);
      composite = toolkit.createComposite(parent);
      if (questionInput.hasChoiceInputs()) {
         createwithChildQuestionControls(toolkit, question, callback);
      }
      else {
         createNoChildQuestionControls(toolkit, question);
      }
   }

   protected void createwithChildQuestionControls(FormToolkit toolkit, Q question, ICreateControlCallback callback) {
      composite.setLayout(new GridLayout(1, false));
      createSection(toolkit, composite, question);
      for (final Choice choice : question.getChoices()) {
         createChoiceControl(toolkit, choice, question);
         QuestionInput[] choiceInputs = getQuestionInput().getChoiceInputs(choice);
         if (!ArrayUtil.isEmpty(choiceInputs)) {
            Composite choiceComposite = toolkit.createComposite(composite);
            GridLayout layout = new GridLayout(1, false);
            layout.marginWidth = 0;
            layout.marginHeight = 0;
            layout.marginLeft = 30;
            layout.horizontalSpacing = 0;
            layout.verticalSpacing = 0;
            choiceComposite.setLayout(layout);
            List<IQuestionInputManager> managers = QuestionWizardPage.createQuestionControls(getWizardPage(), toolkit, choiceComposite, choiceInputs, callback);
            choiceManagers.put(choice, managers);
         }
      }
      updateChoiceChildrenEnabled();
   }
   
   protected void createNoChildQuestionControls(FormToolkit toolkit, Q question) {
      if (question.getLabel() != null) {
         if (question.isVertical()) {
            composite.setLayout(new GridLayout(1, false));
         }
         else {
            composite.setLayout(new GridLayout(question.countChoices() + 1, false));
         }
         createSection(toolkit, composite, question);
      }
      else {
         if (question.isVertical()) {
            composite.setLayout(new GridLayout(1, false));
         }
         else {
            composite.setLayout(new GridLayout(question.countChoices(), false));
         }
      }
      for (final Choice choice : question.getChoices()) {
         createChoiceControl(toolkit, choice, question);
      }
   }
   
   protected void createChoiceControl(final FormToolkit toolkit, final Choice choice, final Q question) {
      final Button button = toolkit.createButton(composite, choice.getText(), getButtonStyle());
      button.setData(choice.getValue());
      if (!StringUtil.isEmpty(choice.getTooltip())) {
         button.setToolTipText(choice.getTooltip() + StringUtil.NEW_LINE + question.getLabel());
      }
      else {
         button.setToolTipText(question.getLabel());
      }
      if (isChoiceSelected(getQuestionInput().getValue(), choice.getValue())) {
         button.setSelection(true);
      }
      button.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleButtonSelected(getQuestionInput(), button, choice);
         }
      });
      buttons.add(button);
      ControlDecoration buttonDecoration = new ControlDecoration(button, SWT.RIGHT | SWT.TOP, button.getParent());
      buttonDecoration.setImage(FieldDecorationRegistry.getDefault().getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
      buttonDecorations.add(buttonDecoration);
      updateButtonDecorations();
   }
   
   protected void updateButtonDecorations() {
      boolean valid = getQuestionInput().validateValue() == null;
      for (ControlDecoration decoration : buttonDecorations) {
         if (valid || !isEnabled() || ((Button) decoration.getControl()).getSelection()) {
            decoration.hide();
         }
         else {
            decoration.show();
         }
      }
   }
   
   protected abstract boolean isChoiceSelected(String inputValue, String choiceValue);

   protected abstract int getButtonStyle();

   protected abstract void handleButtonSelected(QuestionInput questionInput, Button button, Choice choice);

   protected void handleQuestionValueChanged(PropertyChangeEvent evt) {
      for (Button button : buttons) {
         if (isChoiceSelected(ObjectUtil.toString(evt.getNewValue()),
                              ObjectUtil.toString(button.getData()))) {
            button.setSelection(true);
         }
         else {
            button.setSelection(false);
         }
      }
      updateChoiceChildrenEnabled();
      updateButtonDecorations();
   }

   protected void updateValueSetAt(QuestionInput questionInput) {
      if (!questionInput.getPageInput().getPage().isReadonly() &&
          questionInput.getPageInput().getFormInput().getForm().isCollectTimes()) {
         long previousTimes = questionInput.getPageInput().getShownTime();
         long pageShownAt = getWizardPage().getShownAt();
         long now = System.currentTimeMillis();
         questionInput.setValueSetAt(previousTimes + (now - pageShownAt));
      }
   }
   
   @Override
   public void dispose() {
      super.dispose();
      for (List<IQuestionInputManager> managers : choiceManagers.values()) {
         for (IQuestionInputManager manager : managers) {
            manager.dispose();
         }
      }
   }

   public Composite getComposite() {
      return composite;
   }

   @Override
   protected void enableControls(boolean enabled) {
      super.enableControls(enabled);
      for (Button button : buttons) {
         button.setEnabled(enabled);
      }
      updateChoiceChildrenEnabled();
      updateButtonDecorations();
   }
   
   protected void updateChoiceChildrenEnabled() {
      for (Entry<Choice, List<IQuestionInputManager>> entry : choiceManagers.entrySet()) {
         boolean enabled = isEnabled() && isChoiceSelected(getQuestionInput().getValue(), entry.getKey().getValue());
         for (IQuestionInputManager manager : entry.getValue()) {
            manager.setEnabled(enabled);
         }
      }
   }

   @Override
   public Control getFocusControl() {
      Control control = super.getFocusControl();
      if (control == null) {
         control = buttons.get(0);
      }
      return control;
   }
}