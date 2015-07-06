package org.key_project.sed.key.evaluation.wizard.page;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.input.ToolPageInput;
import org.key_project.sed.key.evaluation.wizard.manager.BrowserManager;

public class ToolWizardPage extends AbstractEvaluationWizardPage<ToolPageInput> {
   public ToolWizardPage(ToolPageInput pageInput, ImageDescriptor imageDescriptor) {
      super(pageInput, imageDescriptor);
   }

   @Override
   protected void createContent(FormToolkit toolkit, Composite parent) {
      BrowserManager.createBrowser(toolkit, parent, getPageInput().getPage().getTool().getDescriptionURL());
   }

   @Override
   protected void updatePageCompleted() {
      String errorMessage = getRunnablesFailure();
      setErrornousControl(null);
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }
}
