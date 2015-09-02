package org.key_project.sed.key.evaluation.wizard.manager;

import java.beans.PropertyChangeEvent;

import org.eclipse.jface.fieldassist.ControlDecoration;
import org.eclipse.jface.fieldassist.FieldDecorationRegistry;
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

// TODO: Show different icon when trust is not set.
public class TextManager extends AbstractEditableQuestionInputManager {
   private final Text text;
   
   private final ControlDecoration textDecoration;
   
   public TextManager(AbstractEvaluationWizardPage<?> wizardPage,
                      FormToolkit toolkit, 
                      Composite parent, 
                      QuestionInput questionInput,
                      TextQuestion question) {
      super(wizardPage, questionInput);
      Composite composite = toolkit.createComposite(parent);
      if (parent.getLayout() instanceof GridLayout) {
         composite.setLayoutData(new GridData(GridData.FILL_BOTH));
      }
      composite.setLayout(new GridLayout(1, false));
      createSection(toolkit, composite, question);
      text = toolkit.createText(composite, questionInput.getValue(), SWT.MULTI | SWT.V_SCROLL);
      GridData textData = new GridData(GridData.FILL_BOTH);
      if (question.getWidthHint() > 0) {
         textData.widthHint = question.getWidthHint();
      }
      if (question.getHeightHint() > 0) {
         textData.heightHint = question.getHeightHint();
      }
      text.setLayoutData(textData);
      text.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            handleTextChanged(e);
         }
      });
      textDecoration = new ControlDecoration(text, SWT.RIGHT | SWT.TOP, text.getParent());
      textDecoration.setImage(FieldDecorationRegistry.getDefault().getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
      updateTextDecoration();
   }
   
   protected void updateTextDecoration() {
      if (isEnabled() && getQuestionInput().validateValue() != null) {
         textDecoration.show();
      }
      else {
         textDecoration.hide();
      }
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
      updateTextDecoration();
   }

   @Override
   protected void enableControls(boolean enabled) {
      text.setEnabled(enabled);
      updateTextDecoration();
   }

   @Override
   public Control getFocusControl() {
      return text;
   }
}
