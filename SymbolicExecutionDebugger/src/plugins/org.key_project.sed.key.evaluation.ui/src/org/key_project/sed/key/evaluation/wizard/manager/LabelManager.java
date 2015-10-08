package org.key_project.sed.key.evaluation.wizard.manager;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.key_project.sed.key.evaluation.model.definition.LabelQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.util.eclipse.swt.SWTUtil;

public class LabelManager extends AbstractQuestionInputManager {
   private Label label;
   
   private final QuestionInput questionInput;
   
   private final PropertyChangeListener toolMapListener;
   
   public LabelManager(FormToolkit toolkit, 
                       Composite parent, 
                       QuestionInput questionInput,
                       LabelQuestion question) {
      this.questionInput = questionInput;
      label = toolkit.createLabel(parent, question.getToolSpecificMessage(getCurrentTool()), SWT.WRAP);
      if (parent.getLayout() instanceof TableWrapLayout) {
         label.setLayoutData(new TableWrapData());
      }
      else {
         label.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      }
      PropertyChangeListener toolListener = null;
      if (question.hasToolSpecificMessages()) {
         AbstractPageInput<?> pageInput = questionInput.getPageInput();
         AbstractFormInput<?> formInput = pageInput.getFormInput();
         if (formInput instanceof RandomFormInput) {
            toolListener = new PropertyChangeListener() {
               @Override
               public void propertyChange(PropertyChangeEvent evt) {
                  handleCurrentToolChanged(evt);
               }
            };
            formInput.addPropertyChangeListener(RandomFormInput.PROP_PAGE_TOOL_MAP, toolListener);
         }
      }
      this.toolMapListener = toolListener;
   }
   
   protected void handleCurrentToolChanged(PropertyChangeEvent evt) {
      SWTUtil.setText(label, ((LabelQuestion) questionInput.getQuestion()).getToolSpecificMessage(getCurrentTool()));
   }

   protected Tool getCurrentTool() {
      if (((LabelQuestion) questionInput.getQuestion()).hasToolSpecificMessages()) {
         AbstractPageInput<?> pageInput = questionInput.getPageInput();
         AbstractFormInput<?> formInput = pageInput.getFormInput();
         if (formInput instanceof RandomFormInput) {
            return ((RandomFormInput) formInput).getTool(pageInput);
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   @Override
   public void dispose() {
      if (toolMapListener != null) {
         AbstractPageInput<?> pageInput = questionInput.getPageInput();
         AbstractFormInput<?> formInput = pageInput.getFormInput();
         formInput.removePropertyChangeListener(RandomFormInput.PROP_PAGE_TOOL_MAP, toolMapListener);
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
