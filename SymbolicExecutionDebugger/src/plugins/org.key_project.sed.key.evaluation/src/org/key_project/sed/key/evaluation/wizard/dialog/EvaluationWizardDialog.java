package org.key_project.sed.key.evaluation.wizard.dialog;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.key.evaluation.model_input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model_input.FormInput;
import org.key_project.sed.key.evaluation.model_input.EvaluationInput;
import org.key_project.sed.key.evaluation.wizard.EvaluationWizard;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;

public class EvaluationWizardDialog extends WizardDialog {
   private final EvaluationInput evaluationInput;
   
   private final PropertyChangeListener currentPageListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleCurrentPageChanged(evt);
      }
   };

   public EvaluationWizardDialog(Shell parentShell, EvaluationInput evaluationInput) {
      super(parentShell, new EvaluationWizard(evaluationInput));
      this.evaluationInput = evaluationInput;
      evaluationInput.getCurrentFormInput().addPropertyChangeListener(FormInput.PROP_CURRENT_PAGE_INPUT, currentPageListener);
      setHelpAvailable(false);
   }

   @Override
   protected int getShellStyle() {
      return SWT.CLOSE | SWT.MAX | SWT.TITLE | SWT.BORDER | SWT.RESIZE | getDefaultOrientation();
   }

   @Override
   public void showPage(IWizardPage page) {
      super.showPage(page);
      assert page instanceof AbstractEvaluationWizardPage<?>;
      AbstractEvaluationWizardPage<?> evaluationPage = (AbstractEvaluationWizardPage<?>) page;
      evaluationInput.getCurrentFormInput().setCurrentPageInput(evaluationPage.getPageInput());
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

   @Override
   protected EvaluationWizard getWizard() {
      return (EvaluationWizard)super.getWizard();
   }

   @Override
   public boolean close() {
      evaluationInput.getCurrentFormInput().removePropertyChangeListener(FormInput.PROP_CURRENT_PAGE_INPUT, currentPageListener);
      return super.close();
   }
}
