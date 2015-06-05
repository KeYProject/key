package org.key_project.sed.key.evaluation.wizard.page;

import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.util.LogUtil;
import org.key_project.sed.key.evaluation.util.SEDEvaluationImages;
import org.key_project.sed.key.evaluation.wizard.EvaluationWizard;

public abstract class AbstractEvaluationWizardPage<P extends AbstractPageInput<?>> extends WizardPage {
   private final P pageInput;

   private String runnablesFailure;
   
   private long shownAt;
   
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
   
   @Override
   public EvaluationWizard getWizard() {
      return (EvaluationWizard) super.getWizard();
   }
   
   @Override
   public void setVisible(final boolean visible) {
      super.setVisible(visible);
      if (visible) {
         shownAt = System.currentTimeMillis();
         getWizard().setCurrentPageRunnable(computeRunnable(visible));
      }
      if (!visible) { // The new page is set first to visible before the old page is set to hidden
         if (!pageInput.getPage().isReadonly() && pageInput.getFormInput().getForm().isCollectTimes()) {
            pageInput.addShownTime(System.currentTimeMillis() - shownAt);
         }
         perfomRunnables(computeRunnable(visible), getWizard().getCurrentPageRunnable());
         getWizard().setCurrentPageRunnable(null);
      }
   }
   
   protected IRunnableWithProgress computeRunnable(boolean visible) {
      return null;
   }

   public void perfomRunnables(IRunnableWithProgress hiddenRunnable, 
                               IRunnableWithProgress visibleRunnable) {
      try {
         if (hiddenRunnable != null) {
            getContainer().run(true, false, hiddenRunnable);
         }
         if (visibleRunnable != null) {
            getContainer().run(true, false, visibleRunnable);
         }
      }
      catch (Exception e) {
         runnablesFailure = e.getMessage();
         LogUtil.getLogger().logError(e);
      }
      finally {
         updatePageCompleted();
      }
   }

   public String getRunnablesFailure() {
      return runnablesFailure;
   }

   public long getShownAt() {
      return shownAt;
   }
}
