package org.key_project.sed.key.evaluation.wizard;

import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.key.evaluation.model_input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model_input.FormInput;
import org.key_project.sed.key.evaluation.model_input.EvaluationInput;
import org.key_project.sed.key.evaluation.model_input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model_input.SendFormPageInput;
import org.key_project.sed.key.evaluation.wizard.dialog.EvaluationWizardDialog;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.SendFormWizardPage;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

public class EvaluationWizard extends Wizard {
   private final EvaluationInput evaluationInput;
   
   public EvaluationWizard(EvaluationInput evaluationInput) {
      assert evaluationInput != null;
      this.evaluationInput = evaluationInput;
      setNeedsProgressMonitor(false);
      setHelpAvailable(false);
      setWindowTitle(evaluationInput.getEvaluation().getName());
   }

   @Override
   public void addPages() {
      FormInput form = evaluationInput.getCurrentFormInput();
      if (form != null) {
         for (AbstractPageInput<?> page : form.getPageInputs()) {
            if (page instanceof QuestionPageInput) {
               addPage(new QuestionWizardPage((QuestionPageInput) page));
            }
            else if (page instanceof SendFormPageInput) {
               SendFormPageInput sendPage = (SendFormPageInput) page;
               addPage(new SendFormWizardPage(sendPage, evaluationInput.getFormInput(sendPage.getPage().getForm())));
            }
            else {
               throw new IllegalStateException("Unsupported page input: " + page);
            }
         }
      }
   }

   @Override
   public IWizardPage getStartingPage() {
      return getPage(evaluationInput.getCurrentFormInput().getCurrentPageInput());
   }

   public IWizardPage getPage(final AbstractPageInput<?> pageInput) {
      return ArrayUtil.search(getPages(), new IFilter<IWizardPage>() {
         @Override
         public boolean select(IWizardPage element) {
            return ((AbstractEvaluationWizardPage<?>) element).getPageInput() == pageInput;
         }
      });
   }

   @Override
   public boolean performFinish() {
      return false;
   }

   /**
    * Opens the {@link EvaluationWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param evaluationInput The {@link EvaluationInput} to perform.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, EvaluationInput evaluationInput) {
      EvaluationWizardDialog dialog = new EvaluationWizardDialog(parentShell, evaluationInput);
      return dialog.open();
   }
}
