package org.key_project.sed.key.evaluation.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.key_project.sed.key.evaluation.model_input.AbstractPageInput;

public abstract class AbstractEvaluationWizardPage<P extends AbstractPageInput<?>> extends WizardPage {
   private final P pageInput;

   public AbstractEvaluationWizardPage(P pageInput) {
      super(pageInput.getPage().getName());
      this.pageInput = pageInput;
      setTitle(pageInput.getPage().getTitle());
      setMessage(pageInput.getPage().getMessage());
   }

   @Override
   public void createControl(Composite parent) {
      FormToolkit toolkit = new FormToolkit(parent.getDisplay());
      ScrolledForm form = toolkit.createScrolledForm(parent);
      form.getBody().setLayout(new GridLayout(1, false));
      createContent(toolkit, form);
      setControl(form);
      updatePageCompleted();
   }

   protected abstract void createContent(FormToolkit toolkit, ScrolledForm form);
   
   protected abstract void updatePageCompleted();

   public P getPageInput() {
      return pageInput;
   }
}
