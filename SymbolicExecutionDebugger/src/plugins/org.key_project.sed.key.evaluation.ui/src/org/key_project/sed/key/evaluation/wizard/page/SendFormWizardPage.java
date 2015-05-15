package org.key_project.sed.key.evaluation.wizard.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.SendFormPageInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputWriter;
import org.key_project.sed.key.evaluation.wizard.manager.RadioButtonsManager;
import org.key_project.util.eclipse.swt.SWTUtil;

public class SendFormWizardPage extends AbstractEvaluationWizardPage<SendFormPageInput> {
   private final AbstractFormInput<?> formInput;
   
   private Text contentText;
   
   private RadioButtonsManager acceptManager;
   
   private final PropertyChangeListener acceptListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleAcceptedStateChanged(evt);
      }
   };
   
   public SendFormWizardPage(SendFormPageInput pageInput, AbstractFormInput<?> formInput) {
      super(pageInput);
      this.formInput = formInput;
      pageInput.getAcceptInput().addPropertyChangeListener(QuestionInput.PROP_VALUE, acceptListener);
   }

   @Override
   public void dispose() {
      getPageInput().getAcceptInput().addPropertyChangeListener(QuestionInput.PROP_VALUE, acceptListener);
      acceptManager.dispose();
      super.dispose();
   }

   @Override
   protected void createContent(FormToolkit toolkit, ScrolledForm form) {
      form.getBody().setLayout(new GridLayout(2, false));
      // Content to send
      Label label = toolkit.createLabel(form.getBody(), "&Content to send");
      label.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));
      contentText = toolkit.createText(form.getBody(), EvaluationInputWriter.toFormAnswerXML(formInput), SWT.READ_ONLY | SWT.MULTI);
      contentText.setLayoutData(new GridData(GridData.FILL_BOTH));
      // Additional data stored on server
      toolkit.createLabel(form.getBody(), "Additional &data");
      Text additionalText = toolkit.createText(form.getBody(), getPageInput().getPage().getAdditionalDataCollectedByServer(), SWT.READ_ONLY | SWT.MULTI);
      additionalText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      
      acceptManager = new RadioButtonsManager(toolkit, form.getBody(), getPageInput().getAcceptInput(), (RadioButtonsQuestion) getPageInput().getAcceptInput().getQuestion(), null);
      GridData managerData = new GridData();
      managerData.horizontalSpan = 2;
      acceptManager.getComposite().setLayoutData(managerData);
   }

   @Override
   public void setVisible(boolean visible) {
      if (visible) {
         SWTUtil.setText(contentText, EvaluationInputWriter.toFormAnswerXML(formInput));
      }
      super.setVisible(visible);
   }

   protected void handleAcceptedStateChanged(PropertyChangeEvent evt) {
      updatePageCompleted();
   }

   @Override
   protected void updatePageCompleted() {
      String errorMessage = getPageInput().getAcceptInput().validate();
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }

   public AbstractFormInput<?> getFormInput() {
      return formInput;
   }
}
