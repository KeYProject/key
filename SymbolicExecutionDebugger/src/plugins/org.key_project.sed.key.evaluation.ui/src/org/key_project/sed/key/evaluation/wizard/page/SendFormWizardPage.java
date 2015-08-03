package org.key_project.sed.key.evaluation.wizard.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.widgets.FormToolkit;
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
   
   public SendFormWizardPage(SendFormPageInput pageInput, AbstractFormInput<?> formInput, ImageDescriptor imageDescriptor) {
      super(pageInput, imageDescriptor, false);
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
   protected void createContent(FormToolkit toolkit, Composite parent) {
      parent.setLayout(new GridLayout(2, false));
      // Content to send
      Label label = toolkit.createLabel(parent, "&Content to send");
      label.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));
      contentText = toolkit.createText(parent, EvaluationInputWriter.toFormAnswerXML(formInput), SWT.READ_ONLY | SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
      contentText.setLayoutData(new GridData(GridData.FILL_BOTH));
      // Additional data stored on server
      toolkit.createLabel(parent, "Additional &data");
      Text additionalText = toolkit.createText(parent, getPageInput().getPage().getAdditionalDataCollectedByServer(), SWT.READ_ONLY | SWT.MULTI);
      additionalText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      
      acceptManager = new RadioButtonsManager(this, toolkit, parent, getPageInput().getAcceptInput(), (RadioButtonsQuestion) getPageInput().getAcceptInput().getQuestion(), null);
      GridData managerData = new GridData();
      managerData.horizontalSpan = 2;
      acceptManager.getComposite().setLayoutData(managerData);
   }

   @Override
   public void setVisible(boolean visible) {
      if (visible) {
         // Update shown text asynchronously because this page becomes visible before old page has updated the times.
         getShell().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               SWTUtil.setText(contentText, EvaluationInputWriter.toFormAnswerXML(formInput));
            }
         });
      }
      super.setVisible(visible);
   }

   protected void handleAcceptedStateChanged(PropertyChangeEvent evt) {
      updatePageCompleted();
   }

   @Override
   protected void updatePageCompleted() {
      Control errornousControl = null;
      String errorMessage = getRunnablesFailure();
      if (errorMessage == null) {
         errorMessage = getPageInput().getAcceptInput().validate(null);
         if (errorMessage != null) {
            errornousControl = acceptManager.getComposite();
         }
      }
      setErrornousControl(errornousControl);
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }

   public AbstractFormInput<?> getFormInput() {
      return formInput;
   }
}
