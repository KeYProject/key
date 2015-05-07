package org.key_project.sed.key.evaluation.wizard.dialog;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.SendFormPageInput;
import org.key_project.sed.key.evaluation.wizard.EvaluationWizard;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.SendFormWizardPage;

public class EvaluationWizardDialog extends WizardDialog {
   private final EvaluationInput evaluationInput;
   
   private final PropertyChangeListener currentPageListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleCurrentPageChanged(evt);
      }
   };

   private final PropertyChangeListener sendingListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleSendingInProgressChanged(evt);
      }
   };

   public EvaluationWizardDialog(Shell parentShell, EvaluationInput evaluationInput) {
      super(parentShell, new EvaluationWizard(evaluationInput));
      this.evaluationInput = evaluationInput;
      evaluationInput.getCurrentFormInput().addPropertyChangeListener(AbstractFormInput.PROP_CURRENT_PAGE_INPUT, currentPageListener);
      setHelpAvailable(false);
   }

   @Override
   protected int getShellStyle() {
      return SWT.CLOSE | SWT.MAX | SWT.TITLE | SWT.BORDER | SWT.RESIZE | getDefaultOrientation();
   }

   @Override
   public void showPage(IWizardPage page) {
      if (getCurrentPage() instanceof SendFormWizardPage) {
         ((SendFormWizardPage) getCurrentPage()).getPageInput().removePropertyChangeListener(SendFormPageInput.PROP_SENDING_IN_PROGRESS, sendingListener);
      }
      getWizard().setCurrentPage(page);
      super.showPage(page);
      assert page instanceof AbstractEvaluationWizardPage<?>;
      AbstractEvaluationWizardPage<?> evaluationPage = (AbstractEvaluationWizardPage<?>) page;
      evaluationInput.getCurrentFormInput().setCurrentPageInput(evaluationPage.getPageInput());
      if (page instanceof SendFormWizardPage) {
         ((SendFormWizardPage) page).getPageInput().addPropertyChangeListener(SendFormPageInput.PROP_SENDING_IN_PROGRESS, sendingListener);
      }
   }
   
   @Override
   protected void nextPressed() {
      if (getWizard().nextPressed(getCurrentPage())) {
         super.nextPressed();
      }
   }

   @Override
   protected void finishPressed() {
      super.finishPressed();
      if (getReturnCode() == OK) {
         removeListener();
      }
   }

   @Override
   public AbstractEvaluationWizardPage<?> getCurrentPage() {
      return (AbstractEvaluationWizardPage<?>) super.getCurrentPage();
   }

   protected void handleCurrentPageChanged(PropertyChangeEvent evt) {
      if (evt.getNewValue() != getCurrentPage().getPageInput()) {
         IWizardPage newPage = getWizard().getPage((AbstractPageInput<?>)evt.getNewValue());
         assert newPage != null;
         showPage(newPage);
      }
   }

   protected void handleSendingInProgressChanged(PropertyChangeEvent evt) {
      boolean sendingInProgress = (Boolean)evt.getNewValue();
      if (sendingInProgress) {
         getButton(IDialogConstants.CANCEL_ID).setEnabled(false);
         getButton(IDialogConstants.FINISH_ID).setEnabled(false);
         getButton(IDialogConstants.NEXT_ID).setEnabled(false);
         getButton(IDialogConstants.BACK_ID).setEnabled(false);
      }
      else {
         getButton(IDialogConstants.CANCEL_ID).setEnabled(true);
         getButton(IDialogConstants.FINISH_ID).setEnabled(true);
         getButton(IDialogConstants.NEXT_ID).setEnabled(true);
         getButton(IDialogConstants.BACK_ID).setEnabled(true);
         updateButtons();
      }
   }

   @Override
   protected EvaluationWizard getWizard() {
      return (EvaluationWizard)super.getWizard();
   }

   @Override
   public boolean close() {
      boolean closed = super.close();
      if (closed) {
         removeListener();
      }
      return closed;
   }
   
   protected void removeListener() {
      if (getCurrentPage() instanceof SendFormWizardPage) {
         ((SendFormWizardPage) getCurrentPage()).getPageInput().removePropertyChangeListener(SendFormPageInput.PROP_SENDING_IN_PROGRESS, sendingListener);
      }
      evaluationInput.getCurrentFormInput().removePropertyChangeListener(AbstractFormInput.PROP_CURRENT_PAGE_INPUT, currentPageListener);
   }
}
