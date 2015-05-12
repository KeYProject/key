package org.key_project.sed.key.evaluation.wizard.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.eclipse.ui.services.IDisposable;
import org.key_project.sed.key.evaluation.model.definition.BrowserQuestion;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.tooling.IWorkbenchModifier;
import org.key_project.sed.key.evaluation.util.LogUtil;
import org.key_project.sed.key.evaluation.wizard.manager.RadioButtonsManager;
import org.key_project.util.eclipse.WorkbenchUtil;

public class QuestionWizardPage extends AbstractEvaluationWizardPage<QuestionPageInput> {
   private final List<IDisposable> controls = new LinkedList<IDisposable>();
   
   private final PropertyChangeListener valueListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleValueChange(evt);
      }
   };
   
   private String workbenchModifierFailure;

   public QuestionWizardPage(QuestionPageInput pageInput) {
      super(pageInput);
   }

   @Override
   public void dispose() {
      for (QuestionInput questionInput : getPageInput().getQuestionInputs()) {
         questionInput.removePropertyChangeListener(QuestionInput.PROP_VALUE, valueListener);
      }
      for (IDisposable control : controls) {
         control.dispose();
      }
      super.dispose();
   }

   @Override
   protected void createContent(FormToolkit toolkit, ScrolledForm form) {
      for (QuestionInput questionInput : getPageInput().getQuestionInputs()) {
         questionInput.addPropertyChangeListener(QuestionInput.PROP_VALUE, valueListener);
         if (questionInput.getQuestion() instanceof BrowserQuestion) {
            createBrowser(toolkit, form.getBody(), (BrowserQuestion) questionInput.getQuestion());
         }
         else if (questionInput.getQuestion() instanceof RadioButtonsQuestion) {
            createRadioButtons(toolkit, form.getBody(), questionInput, (RadioButtonsQuestion) questionInput.getQuestion());
         }
         else {
            throw new IllegalStateException("Unsupported question: " + questionInput.getQuestion());
         }
      }
   }

   protected void createBrowser(FormToolkit toolkit, Composite parent, BrowserQuestion question) {
      createBrowser(toolkit, parent, question.getUrl());
   }
   
   public static Browser createBrowser(FormToolkit toolkit, Composite parent, URL url) {
      Browser browser = new Browser(parent, SWT.BORDER);
      toolkit.adapt(browser);
      browser.setLayoutData(new GridData(GridData.FILL_BOTH));
      browser.setMenu(new MenuManager().createContextMenu(browser)); // Disable context menu
      try {
         URL fileUrl = FileLocator.toFileURL(url); 
         browser.setUrl(fileUrl.toString());
      }
      catch (IOException e) {
         browser.setText(e.getMessage());
      }
      return browser;
   }

   protected void createRadioButtons(FormToolkit toolkit, Composite parent, QuestionInput questionInput, RadioButtonsQuestion question) {
      RadioButtonsManager manager = new RadioButtonsManager(toolkit, parent, questionInput, question);
      controls.add(manager);
   }

   protected void handleValueChange(PropertyChangeEvent evt) {
      updatePageCompleted();
   }
   
   @Override
   protected void updatePageCompleted() {
      String errorMessage = workbenchModifierFailure;
      // Validate questions
      if (errorMessage == null) {
         QuestionInput[] inputs = getPageInput().getQuestionInputs();
         int i = 0;
         while (errorMessage == null && i < inputs.length) {
            errorMessage = inputs[i].validate();
            i++;
         }
      }
      // Update page completed state
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }

   @Override
   public void setVisible(final boolean visible) {
      super.setVisible(visible);
      try {
         final IWorkbenchModifier modifier = getPageInput().getPage().getWorkbenchModifier();
         final Tool tool = getPageInput().getFormInput() instanceof RandomFormInput ?
                           ((RandomFormInput) getPageInput().getFormInput()).getTool(getPageInput()) :
                           null;
         if (modifier != null) {
            final IWorkbenchPage activePage = WorkbenchUtil.getActivePage(); 
            getContainer().run(true, false, new IRunnableWithProgress() {
               @Override
               public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
                  try {
                     if (visible) {
                        monitor.beginTask("Modifying Workbench", IProgressMonitor.UNKNOWN);
                        modifier.init(activePage, getShell(), getPageInput(), tool);
                        modifier.modifyWorkbench();
                        monitor.done();
                     }
                     else {
                        monitor.beginTask("Cleaning Workbench", IProgressMonitor.UNKNOWN);
                        modifier.cleanWorkbench();
                        monitor.done();
                     }
                  }
                  catch (Exception e) {
                     throw new InvocationTargetException(e, e.getMessage());
                  }
               }
            });
         }
      }
      catch (Exception e) {
         workbenchModifierFailure = e.getMessage();
         LogUtil.getLogger().logError(e);
      }
      finally {
         updatePageCompleted();
      }
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
