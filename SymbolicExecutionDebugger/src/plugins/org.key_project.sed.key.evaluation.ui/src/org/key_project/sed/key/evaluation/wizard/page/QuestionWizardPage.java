package org.key_project.sed.key.evaluation.wizard.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.lang.reflect.InvocationTargetException;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.eclipse.ui.services.IDisposable;
import org.key_project.sed.key.evaluation.model.definition.BrowserQuestion;
import org.key_project.sed.key.evaluation.model.definition.CheckboxQuestion;
import org.key_project.sed.key.evaluation.model.definition.LabelQuestion;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.definition.SectionQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.tooling.IWorkbenchModifier;
import org.key_project.sed.key.evaluation.wizard.manager.BrowserManager;
import org.key_project.sed.key.evaluation.wizard.manager.CheckboxManager;
import org.key_project.sed.key.evaluation.wizard.manager.IQuestionInputManager;
import org.key_project.sed.key.evaluation.wizard.manager.LabelManager;
import org.key_project.sed.key.evaluation.wizard.manager.RadioButtonsManager;
import org.key_project.sed.key.evaluation.wizard.manager.SectionManager;
import org.key_project.util.eclipse.WorkbenchUtil;

public class QuestionWizardPage extends AbstractEvaluationWizardPage<QuestionPageInput> {
   private final List<IDisposable> controls = new LinkedList<IDisposable>();
   
   private final PropertyChangeListener valueAndTrustListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleValueOrTrustChange(evt);
      }
   };
   
   private final Set<QuestionInput> observedInputs = new HashSet<QuestionInput>();

   public QuestionWizardPage(QuestionPageInput pageInput) {
      super(pageInput);
   }

   @Override
   public void dispose() {
      for (QuestionInput questionInput : observedInputs) {
         questionInput.removePropertyChangeListener(QuestionInput.PROP_VALUE, valueAndTrustListener);
         questionInput.removePropertyChangeListener(QuestionInput.PROP_TRUST, valueAndTrustListener);
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
            questionInput.addPropertyChangeListener(QuestionInput.PROP_VALUE, valueAndTrustListener);
            questionInput.addPropertyChangeListener(QuestionInput.PROP_TRUST, valueAndTrustListener);
            observedInputs.add(questionInput);
         }
      };
      List<IQuestionInputManager> managers = createQuestionControls(this,
                                                                    toolkit, 
                                                                    form.getBody(), 
                                                                    getPageInput().getQuestionInputs(),
                                                                    callBack);
      controls.addAll(managers);
   }
   
   public static List<IQuestionInputManager> createQuestionControls(AbstractEvaluationWizardPage<?> wizardPage,
                                                                    FormToolkit toolkit, 
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
            IQuestionInputManager manager = createRadioButtons(wizardPage, toolkit, parent, questionInput, (RadioButtonsQuestion) questionInput.getQuestion(), callback);
            managers.add(manager);
         }
         else if (questionInput.getQuestion() instanceof CheckboxQuestion) {
            IQuestionInputManager manager = createCheckboxes(wizardPage, toolkit, parent, questionInput, (CheckboxQuestion) questionInput.getQuestion(), callback);
            managers.add(manager);
         }
         else if (questionInput.getQuestion() instanceof LabelQuestion) {
            IQuestionInputManager manager = createLabel(toolkit, parent, (LabelQuestion) questionInput.getQuestion());
            managers.add(manager);
         }
         else if (questionInput.getQuestion() instanceof SectionQuestion) {
            IQuestionInputManager manager = createSection(wizardPage, toolkit, parent, questionInput, (SectionQuestion) questionInput.getQuestion(), callback);
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

   public static RadioButtonsManager createRadioButtons(AbstractEvaluationWizardPage<?> wizardPage, FormToolkit toolkit, Composite parent, QuestionInput questionInput, RadioButtonsQuestion question, ICreateControlCallback callback) {
      return new RadioButtonsManager(wizardPage, toolkit, parent, questionInput, question, callback);
   }

   public static CheckboxManager createCheckboxes(AbstractEvaluationWizardPage<?> wizardPage, FormToolkit toolkit, Composite parent, QuestionInput questionInput, CheckboxQuestion question, ICreateControlCallback callback) {
      return new CheckboxManager(wizardPage, toolkit, parent, questionInput, question, callback);
   }

   public static LabelManager createLabel(FormToolkit toolkit, Composite parent, LabelQuestion question) {
      return new LabelManager(toolkit, parent, question);
   }

   public static SectionManager createSection(AbstractEvaluationWizardPage<?> wizardPage, FormToolkit toolkit, Composite parent, QuestionInput questionInput, SectionQuestion question, ICreateControlCallback callback) {
      return new SectionManager(wizardPage, toolkit, parent, questionInput, question, callback);
   }
   
   public static interface ICreateControlCallback {
      public void handleQuestionInput(QuestionInput questionInput);
   }

   protected void handleValueOrTrustChange(PropertyChangeEvent evt) {
      updatePageCompleted();
   }
   
   @Override
   protected void updatePageCompleted() {
      String errorMessage = getRunnablesFailure();
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
   protected IRunnableWithProgress computeRunnable(final boolean visible) {
      final IWorkbenchModifier modifier = getPageInput().getPage().getWorkbenchModifier();
      if (modifier != null) {
         final Tool tool = getPageInput().getFormInput() instanceof RandomFormInput ?
                           ((RandomFormInput) getPageInput().getFormInput()).getTool(getPageInput()) :
                           null;
         final IWorkbenchPage activePage = WorkbenchUtil.getActivePage();
         return new IRunnableWithProgress() {
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
         };
      }
      else {
         return null;
      }
   }
}
