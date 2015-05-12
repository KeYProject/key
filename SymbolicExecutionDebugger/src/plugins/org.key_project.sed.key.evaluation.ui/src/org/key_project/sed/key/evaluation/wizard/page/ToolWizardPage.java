package org.key_project.sed.key.evaluation.wizard.page;

import org.eclipse.swt.layout.GridLayout;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.key_project.sed.key.evaluation.model.input.ToolPageInput;

public class ToolWizardPage extends AbstractEvaluationWizardPage<ToolPageInput> {
   public ToolWizardPage(ToolPageInput pageInput) {
      super(pageInput);
   }

   @Override
   protected void createContent(FormToolkit toolkit, ScrolledForm form) {
      form.getBody().setLayout(new GridLayout(1, false));
      QuestionWizardPage.createBrowser(toolkit, form.getBody(), getPageInput().getPage().getTool().getDescriptionURL());
   }

   @Override
   protected void updatePageCompleted() {
   }
}
