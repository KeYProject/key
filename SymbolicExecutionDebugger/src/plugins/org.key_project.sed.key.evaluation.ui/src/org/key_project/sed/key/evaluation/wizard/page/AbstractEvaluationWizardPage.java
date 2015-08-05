package org.key_project.sed.key.evaluation.wizard.page;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.SharedScrolledComposite;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.key_project.sed.key.evaluation.model.definition.IPageWithWorkbenchModifier;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.tooling.IWorkbenchModifier;
import org.key_project.sed.key.evaluation.util.LogUtil;
import org.key_project.sed.key.evaluation.wizard.EvaluationWizard;
import org.key_project.sed.key.evaluation.wizard.dialog.EvaluationWizardDialog;
import org.key_project.sed.key.evaluation.wizard.manager.TabbedManager;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.thread.AbstractRunnableWithProgressAndResult;
import org.key_project.util.thread.IRunnableWithProgressAndResult;

public abstract class AbstractEvaluationWizardPage<P extends AbstractPageInput<?>> extends WizardPage {
   private final P pageInput;

   private String runnablesFailure;
   
   private long shownAt;
   
   private Control errornousControl;
   
   private SharedScrolledComposite form;
   
   private final boolean useForm;
   
   public AbstractEvaluationWizardPage(P pageInput, ImageDescriptor imageDescriptor, boolean useForm) {
      super(pageInput.getPage().getName());
      this.pageInput = pageInput;
      this.useForm = useForm;
      setTitle(pageInput.getPage().getTitle());
      setMessage(pageInput.getPage().getMessage());
      setImageDescriptor(imageDescriptor);
   }

   @Override
   public void createControl(Composite parent) {
      FormToolkit toolkit = new FormToolkit(parent.getDisplay());
      if (useForm) {
         // Tutorial about Forms: https://eclipse.org/articles/Article-Forms/article.html
         form = new SharedScrolledComposite(parent, SWT.H_SCROLL | SWT.V_SCROLL) {};
         toolkit.adapt(form);
         Composite content = toolkit.createComposite(form);
         if (getPageInput().getPage().isWrapLayout()) {
            content.setLayout(new TableWrapLayout());
         }
         else {
            content.setLayout(new GridLayout(1, false));
         }
         form.setContent(content);
         form.setExpandHorizontal(true);
         form.setExpandVertical(true);
         createContent(toolkit, content);
         setControl(form);
      }
      else {
         Composite content = toolkit.createComposite(parent);
         if (getPageInput().getPage().isWrapLayout()) {
            content.setLayout(new TableWrapLayout());
         }
         else {
            content.setLayout(new GridLayout(1, false));
         }
         createContent(toolkit, content);
         setControl(content);
      }
      updatePageCompleted();
   }

   protected abstract void createContent(FormToolkit toolkit, Composite parent);
   
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
         if (isPerformWorkbenchModifierAutomatically()) {
            getWizard().setCurrentPageRunnable(computeRunnable(visible));
         }
      }
      if (!visible) { // The new page is set first to visible before the old page is set to hidden
         if (!pageInput.getPage().isReadonly() && pageInput.getFormInput().getForm().isCollectTimes()) {
            pageInput.addShownTime(System.currentTimeMillis() - shownAt);
         }
         final IRunnableWithProgressAndResult<String> hiddenRunnable = computeRunnable(visible);
         final IRunnableWithProgressAndResult<String> visibleRunnable = getWizard().getCurrentPageRunnable();
         getWizard().setCurrentPageRunnable(null);
         getShell().getDisplay().asyncExec(new Runnable() { // Execute runnables asynchronously to ensure that title and toolbar is already updated.
            @Override
            public void run() {
               perfomRunnables(hiddenRunnable, visibleRunnable);
               // Update the shown at time after the runnables are executed (loading times are ignored)
               ((EvaluationWizardDialog) getContainer()).getCurrentPage().updateShownAt();
            }
         });
      }
   }
   
   public boolean isPerformWorkbenchModifierAutomatically() {
      return true;
   }
   
   public void updateShownAt() {
      shownAt = System.currentTimeMillis();
   }

   public IRunnableWithProgressAndResult<String> computeRunnable(final boolean visible) {
      if (getPageInput().getPage() instanceof IPageWithWorkbenchModifier) {
         final IWorkbenchModifier modifier = ((IPageWithWorkbenchModifier) getPageInput().getPage()).getWorkbenchModifier();
         if (modifier != null) {
            final Tool tool = getCurrentTool();
            final IWorkbenchPage activePage = WorkbenchUtil.getActivePage();
            return new AbstractRunnableWithProgressAndResult<String>() {
               @Override
               public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
                  try {
                     if (visible) {
                        monitor.beginTask("Modifying Workbench, Please wait...", IProgressMonitor.UNKNOWN);
                        modifier.init(activePage, getShell(), getPageInput(), tool);
                        String completionMessage = modifier.modifyWorkbench();
                        monitor.done();
                        setResult(completionMessage);
                     }
                     else {
                        monitor.beginTask("Cleaning Workbench, Please wait...", IProgressMonitor.UNKNOWN);
                        modifier.cleanWorkbench();
                        monitor.done();
                        setResult(null);
                     }
                  }
                  catch (Exception e) {
                     throw new InvocationTargetException(e, e.getMessage());
                  }
               }
            };
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
   
   protected Tool getCurrentTool() {
      return getPageInput().getFormInput() instanceof RandomFormInput ?
             ((RandomFormInput) getPageInput().getFormInput()).getTool(getPageInput()) :
             null;
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
   
   public final void performMessageClick() {
      String newTab = null;
      if (errornousControl != null) {
         Control current = errornousControl;
         // Ensure that control is visible
         while (current != getControl()) {
            Composite parent = current.getParent();
            if (parent instanceof CTabFolder) {
               final Control controlOfTabItem = current;
               CTabFolder tabFolder = (CTabFolder) parent;
               CTabItem tabItem = ArrayUtil.search(tabFolder.getItems(), new IFilter<CTabItem>() {
                  @Override
                  public boolean select(CTabItem element) {
                     return element.getControl() == controlOfTabItem;
                  }
               });
               if (!ObjectUtil.equals(tabFolder.getSelection(), tabItem)) {
                  tabFolder.setSelection(tabItem);
                  if (tabFolder.getData() instanceof TabbedManager) {
                     ((TabbedManager) tabFolder.getData()).handleSelectedTabChanged();
                  }
                  newTab = tabItem.getText();
               }
            }
            else if (parent instanceof ScrolledComposite) {
               ((ScrolledComposite) parent).showControl(errornousControl);
            }
            current = parent;
         }
         // Scroll to control
         if (form != null) {
            form.showControl(errornousControl);
         }
         if (newTab != null) {
            MessageDialog.openInformation(getShell(), "Selected tab has changed", "Please answer the questions of tab '" + newTab + ".");
         }
      }
   }
   
   public void reflow() {
      if (form != null) {
         form.reflow(true);
      }
   }

   @Override
   protected EvaluationWizardDialog getContainer() {
      return (EvaluationWizardDialog) super.getContainer();
   }
}
