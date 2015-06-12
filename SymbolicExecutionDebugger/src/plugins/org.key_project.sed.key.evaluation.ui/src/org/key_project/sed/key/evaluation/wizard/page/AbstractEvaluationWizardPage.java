package org.key_project.sed.key.evaluation.wizard.page;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.util.LogUtil;
import org.key_project.sed.key.evaluation.util.SEDEvaluationImages;
import org.key_project.sed.key.evaluation.wizard.EvaluationWizard;
import org.key_project.util.thread.IRunnableWithProgressAndResult;

public abstract class AbstractEvaluationWizardPage<P extends AbstractPageInput<?>> extends WizardPage {
   private final P pageInput;

   private String runnablesFailure;
   
   private long shownAt;
   
   private Control errornousControl;
   
   private ScrolledForm form;
   
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
      form = toolkit.createScrolledForm(parent);
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
   
   protected IRunnableWithProgressAndResult<String> computeRunnable(boolean visible) {
      return null;
   }

   public void perfomRunnables(IRunnableWithProgressAndResult<String> hiddenRunnable, 
                               IRunnableWithProgressAndResult<String> visibleRunnable) {
      try {
         final String hiddenCompletionMessage;
         if (hiddenRunnable != null) {
            getContainer().run(true, false, hiddenRunnable);
            hiddenCompletionMessage = hiddenRunnable.getResult();
         }
         else {
            hiddenCompletionMessage = null;
         }
         final String visibleCompletionMessage;
         if (visibleRunnable != null) {
            getContainer().run(true, false, visibleRunnable);
            visibleCompletionMessage = visibleRunnable.getResult();
         }
         else {
            visibleCompletionMessage = null;
         }
         if (hiddenRunnable != null || visibleRunnable != null) {
            getShell().forceActive();
            getShell().forceFocus();
         }
         if (hiddenCompletionMessage != null || visibleCompletionMessage != null) {
            getShell().getDisplay().asyncExec(new Runnable() {
               @Override
               public void run() {
                  if (hiddenCompletionMessage != null) {
                     MessageDialog.openInformation(getShell(), "Information", hiddenCompletionMessage);
                  }
                  if (visibleCompletionMessage != null) {
                     MessageDialog.openInformation(getShell(), "Information", visibleCompletionMessage);            
                  }
               }
            });
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
   
   public Control getErrornousControl() {
      return errornousControl;
   }

   public void setErrornousControl(Control errornousControl) {
      this.errornousControl = errornousControl;
   }

   public boolean isMessageClickable() {
      return errornousControl != null;
   }
   
   public void performMessageClick() {
      if (errornousControl != null) {
         form.showControl(errornousControl);
      }
   }
}
