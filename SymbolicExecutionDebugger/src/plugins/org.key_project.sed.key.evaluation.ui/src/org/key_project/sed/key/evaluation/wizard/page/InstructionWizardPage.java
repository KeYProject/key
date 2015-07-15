package org.key_project.sed.key.evaluation.wizard.page;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.input.InstructionPageInput;
import org.key_project.sed.key.evaluation.wizard.manager.BrowserManager;

public class InstructionWizardPage extends AbstractEvaluationWizardPage<InstructionPageInput> {
   public InstructionWizardPage(InstructionPageInput pageInput, ImageDescriptor imageDescriptor) {
      super(pageInput, imageDescriptor, true);
   }

   @Override
   protected void createContent(FormToolkit toolkit, Composite parent) {
      BrowserManager.createBrowser(toolkit, parent, getPageInput().getPage().getDescriptionURL());
   }

   @Override
   protected void updatePageCompleted() {
      String errorMessage = getRunnablesFailure();
      setErrornousControl(null);
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }
}
