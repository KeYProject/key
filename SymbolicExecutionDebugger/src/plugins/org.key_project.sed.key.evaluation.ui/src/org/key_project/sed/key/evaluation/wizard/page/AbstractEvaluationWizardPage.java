package org.key_project.sed.key.evaluation.wizard.page;

import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.util.SEDEvaluationImages;

public abstract class AbstractEvaluationWizardPage<P extends AbstractPageInput<?>> extends WizardPage {
   private final P pageInput;

   public AbstractEvaluationWizardPage(P pageInput) {
      super(pageInput.getPage().getName());
      this.pageInput = pageInput;
      setTitle(pageInput.getPage().getTitle());
      setMessage(pageInput.getPage().getMessage());
      setImageDescriptor(SEDEvaluationImages.getImageDescriptor(SEDEvaluationImages.EVALUATION_WIZARD));
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

   @Override
   public IWizardPage getPreviousPage() {
      return getWizard().getPreviousPage(this); // Avoid that the previously shown page is returned
   }

   @Override
   public IWizardPage getNextPage() {
      return getWizard().getNextPage(this);
   }
}
