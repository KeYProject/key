package org.key_project.sed.key.evaluation.wizard.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.lang.reflect.InvocationTargetException;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
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
import org.key_project.sed.key.evaluation.wizard.manager.BrowserManager;
import org.key_project.sed.key.evaluation.wizard.manager.IQuestionInputManager;
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
      ICreateControlCallback callBack = new ICreateControlCallback() {
         @Override
         public void handleQuestionInput(QuestionInput questionInput) {
            questionInput.addPropertyChangeListener(QuestionInput.PROP_VALUE, valueListener);
         }
      };
      List<IQuestionInputManager> managers = createQuestionControls(toolkit, 
                                                                    form.getBody(), 
                                                                    getPageInput().getQuestionInputs(),
                                                                    callBack);
      controls.addAll(managers);
   }
   
   public static List<IQuestionInputManager> createQuestionControls(FormToolkit toolkit, 
                                                                    Composite parent, 
                                                                    QuestionInput[] questionInputs,
                                                                    ICreateControlCallback callback) {
      List<IQuestionInputManager> managers = new LinkedList<IQuestionInputManager>();
      for (QuestionInput questionInput : questionInputs) {
         callback.handleQuestionInput(questionInput);
         if (questionInput.getQuestion() instanceof BrowserQuestion) {
            IQuestionInputManager manager = createBrowser(toolkit, parent, (BrowserQuestion) questionInput.getQuestion());
            managers.add(manager);
         }
         else if (questionInput.getQuestion() instanceof RadioButtonsQuestion) {
            IQuestionInputManager manager = createRadioButtons(toolkit, parent, questionInput, (RadioButtonsQuestion) questionInput.getQuestion(), callback);
            managers.add(manager);
         }
         else {
            throw new IllegalStateException("Unsupported question: " + questionInput.getQuestion());
         }
      }
      return managers;
   }

   public static BrowserManager createBrowser(FormToolkit toolkit, Composite parent, BrowserQuestion question) {
      return new BrowserManager(toolkit, parent, question);
   }

   public static RadioButtonsManager createRadioButtons(FormToolkit toolkit, Composite parent, QuestionInput questionInput, RadioButtonsQuestion question, ICreateControlCallback callback) {
      return new RadioButtonsManager(toolkit, parent, questionInput, question, callback);
   }
   
   public static interface ICreateControlCallback {
      public void handleQuestionInput(QuestionInput questionInput);
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
}
