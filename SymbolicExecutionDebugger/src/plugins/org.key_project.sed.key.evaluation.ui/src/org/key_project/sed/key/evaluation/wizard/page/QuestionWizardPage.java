package org.key_project.sed.key.evaluation.wizard.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.services.IDisposable;
import org.key_project.sed.key.evaluation.model.definition.BrowserQuestion;
import org.key_project.sed.key.evaluation.model.definition.CheckboxQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.ImageQuestion;
import org.key_project.sed.key.evaluation.model.definition.LabelQuestion;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.definition.SectionQuestion;
import org.key_project.sed.key.evaluation.model.definition.TabQuestion;
import org.key_project.sed.key.evaluation.model.definition.TabbedQuestion;
import org.key_project.sed.key.evaluation.model.definition.TextQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.wizard.manager.BrowserManager;
import org.key_project.sed.key.evaluation.wizard.manager.CheckboxManager;
import org.key_project.sed.key.evaluation.wizard.manager.IQuestionInputManager;
import org.key_project.sed.key.evaluation.wizard.manager.IReflowParticipant;
import org.key_project.sed.key.evaluation.wizard.manager.ImageManager;
import org.key_project.sed.key.evaluation.wizard.manager.LabelManager;
import org.key_project.sed.key.evaluation.wizard.manager.RadioButtonsManager;
import org.key_project.sed.key.evaluation.wizard.manager.SectionManager;
import org.key_project.sed.key.evaluation.wizard.manager.TabManager;
import org.key_project.sed.key.evaluation.wizard.manager.TabbedManager;
import org.key_project.sed.key.evaluation.wizard.manager.TextManager;
import org.key_project.util.java.ArrayUtil;

public class QuestionWizardPage extends AbstractEvaluationWizardPage<QuestionPageInput> {
   private final List<IQuestionInputManager> controls = new LinkedList<IQuestionInputManager>();
   
   private final PropertyChangeListener valueAndTrustListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleValueOrTrustChange(evt);
      }
   };
   
   private final Set<QuestionInput> observedInputs = new HashSet<QuestionInput>();
   
   private final Map<QuestionInput, IQuestionInputManager> input2managerMap = new HashMap<QuestionInput, IQuestionInputManager>();
   
   private FormToolkit toolkit;

   private Composite parent;
   
   public QuestionWizardPage(QuestionPageInput pageInput, ImageDescriptor imageDescriptor) {
      super(pageInput, imageDescriptor, pageInput.getPage().isUseForm());
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
   protected void createContent(FormToolkit toolkit, Composite parent) {
      // Nothing to do, content is created when wizard page becomes visible the first time.
      this.toolkit = toolkit;
      this.parent = parent;
   }
   
   public void ensureContentIsCreated() {
      if (parent != null && toolkit != null) {
         ICreateControlCallback callBack = new ICreateControlCallback() {
            @Override
            public void handleQuestionInput(QuestionInput questionInput) {
               questionInput.addPropertyChangeListener(QuestionInput.PROP_VALUE, valueAndTrustListener);
               questionInput.addPropertyChangeListener(QuestionInput.PROP_TRUST, valueAndTrustListener);
               observedInputs.add(questionInput);
            }

            @Override
            public void handleManagerCreated(QuestionInput questionInput, IQuestionInputManager manager) {
               input2managerMap.put(questionInput, manager);
            }
         };
         List<IQuestionInputManager> managers = createQuestionControls(this,
                                                                       toolkit, 
                                                                       parent, 
                                                                       getPageInput().getQuestionInputs(),
                                                                       callBack);
         controls.addAll(managers);
         reflow();
         toolkit = null;
         parent = null;
         updatePageCompleted();
      }
   }

   public static List<IQuestionInputManager> createQuestionControls(AbstractEvaluationWizardPage<?> wizardPage,
                                                                    FormToolkit toolkit, 
                                                                    Composite parent, 
                                                                    QuestionInput[] questionInputs,
                                                                    ICreateControlCallback callback) {
      List<IQuestionInputManager> managers = new LinkedList<IQuestionInputManager>();
      for (QuestionInput questionInput : questionInputs) {
         callback.handleQuestionInput(questionInput);
         if (questionInput.getQuestion().isEnabled() &&
             (!questionInput.getQuestion().isToolRelated() ||
              ArrayUtil.contains(questionInput.getQuestion().getRelatedTools(), wizardPage.getCurrentTool()))) {
            IQuestionInputManager manager;
            if (questionInput.getQuestion() instanceof BrowserQuestion) {
               manager = createBrowser(toolkit, parent, (BrowserQuestion) questionInput.getQuestion());
            }
            else if (questionInput.getQuestion() instanceof RadioButtonsQuestion) {
               manager = createRadioButtons(wizardPage, toolkit, parent, questionInput, (RadioButtonsQuestion) questionInput.getQuestion(), callback);
            }
            else if (questionInput.getQuestion() instanceof CheckboxQuestion) {
               manager = createCheckboxes(wizardPage, toolkit, parent, questionInput, (CheckboxQuestion) questionInput.getQuestion(), callback);
            }
            else if (questionInput.getQuestion() instanceof LabelQuestion) {
               manager = createLabel(toolkit, parent, questionInput, (LabelQuestion) questionInput.getQuestion());
            }
            else if (questionInput.getQuestion() instanceof ImageQuestion) {
               manager = createImage(toolkit, parent, (ImageQuestion) questionInput.getQuestion());
            }
            else if (questionInput.getQuestion() instanceof SectionQuestion) {
               manager = createSection(wizardPage, toolkit, parent, questionInput, (SectionQuestion) questionInput.getQuestion(), callback);
            }
            else if (questionInput.getQuestion() instanceof TextQuestion) {
               manager = createText(wizardPage, toolkit, parent, questionInput, (TextQuestion) questionInput.getQuestion());
            }
            else if (questionInput.getQuestion() instanceof TabbedQuestion) {
               manager = createTabbed(wizardPage, toolkit, parent, questionInput, (TabbedQuestion) questionInput.getQuestion(), callback);
            }
            else if (questionInput.getQuestion() instanceof TabQuestion) {
               manager = createTab(wizardPage, toolkit, parent, questionInput, (TabQuestion) questionInput.getQuestion(), callback);
            }
            else {
               throw new IllegalStateException("Unsupported question: " + questionInput.getQuestion());
            }
            managers.add(manager);
            callback.handleManagerCreated(questionInput, manager);
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

   public static LabelManager createLabel(FormToolkit toolkit, Composite parent, QuestionInput questionInput, LabelQuestion question) {
      return new LabelManager(toolkit, parent, questionInput, question);
   }

   public static ImageManager createImage(FormToolkit toolkit, Composite parent, ImageQuestion question) {
      return new ImageManager(toolkit, parent, question);
   }

   public static SectionManager createSection(AbstractEvaluationWizardPage<?> wizardPage, FormToolkit toolkit, Composite parent, QuestionInput questionInput, SectionQuestion question, ICreateControlCallback callback) {
      return new SectionManager(wizardPage, toolkit, parent, questionInput, question, callback);
   }

   public static TabbedManager createTabbed(AbstractEvaluationWizardPage<?> wizardPage, FormToolkit toolkit, Composite parent, QuestionInput questionInput, TabbedQuestion question, ICreateControlCallback callback) {
      return new TabbedManager(wizardPage, toolkit, parent, questionInput, question, callback);
   }

   public static TabManager createTab(AbstractEvaluationWizardPage<?> wizardPage, FormToolkit toolkit, Composite parent, QuestionInput questionInput, TabQuestion question, ICreateControlCallback callback) {
      return new TabManager(wizardPage, toolkit, parent, questionInput, question, callback);
   }

   public static TextManager createText(AbstractEvaluationWizardPage<?> wizardPage, FormToolkit toolkit, Composite parent, QuestionInput questionInput, TextQuestion question) {
      return new TextManager(wizardPage, toolkit, parent, questionInput, question);
   }
   
   public static interface ICreateControlCallback {
      public void handleQuestionInput(QuestionInput questionInput);
      
      public void handleManagerCreated(QuestionInput questionInput, IQuestionInputManager manager);
   }

   protected void handleValueOrTrustChange(PropertyChangeEvent evt) {
      updatePageCompleted();
   }
   
   @Override
   protected void updatePageCompleted() {
      Control errornousControl = null;
      String errorMessage = getRunnablesFailure();
      // Validate questions
      if (parent == null) { // Validate input only if controls have been created
         Tool tool = getCurrentTool();
         if (errorMessage == null) {
            QuestionInput[] inputs = getPageInput().getQuestionInputs();
            int i = 0;
            while (errorMessage == null && i < inputs.length) {
               errorMessage = inputs[i].validate(tool);
               if (errorMessage != null) {
                  if (isInputErrornous(inputs[i], tool)) {
                     IQuestionInputManager errornousManager = input2managerMap.get(inputs[i]);
                     if (errornousManager != null) {
                        errornousControl = errornousManager.getFocusControl();
                     }
                  }
                  else {
                     QuestionInput errornousInput = findErrornousInput(inputs[i]);
                     if (errornousInput != null) {
                        IQuestionInputManager errornousManager = input2managerMap.get(errornousInput);
                        if (errornousManager != null) {
                           errornousControl = errornousManager.getFocusControl();
                        }
                     }
                  }
               }
               i++;
            }
         }
      }
      // Update page completed state
      setErrornousControl(errornousControl);
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }

   protected QuestionInput findErrornousInput(QuestionInput questionInput) {
      QuestionInput errornousInput = null;
      // Search in choice inputs
      Tool currentTool = getCurrentTool();
      if (questionInput.hasChoiceInputs()) {
         Choice[] selectedChoices = questionInput.getSelectedChoices();
         for (int i = 0; errornousInput == null && i < selectedChoices.length; i++) {
            QuestionInput[] childInputs = questionInput.getChoiceInputs(selectedChoices[i]);
            if (childInputs != null) {
               for (int j = 0; errornousInput == null && j < childInputs.length; j++) {
                  if (isInputErrornous(childInputs[j], currentTool)) {
                     errornousInput = childInputs[j];
                  }
                  else {
                     errornousInput = findErrornousInput(childInputs[j]);
                  }
               }
            }
         }
      }
      // Search in child inputs
      if (errornousInput == null && questionInput.countChildInputs() > 0) {
         QuestionInput[] childInputs = questionInput.getChildInputs();
         for (int i = 0; errornousInput == null && i < childInputs.length; i++) {
            if (isInputErrornous(childInputs[i], currentTool)) {
               errornousInput = childInputs[i];
            }
            else {
               errornousInput = findErrornousInput(childInputs[i]);
            }
         }
      }
      return errornousInput;
   }
   
   protected boolean isInputErrornous(QuestionInput questionInput, Tool currentTool) {
      if (questionInput.getQuestion().isEnabled() &&
          (!questionInput.getQuestion().isToolRelated() ||
           ArrayUtil.contains(questionInput.getQuestion().getRelatedTools(), currentTool))) {
         return questionInput.validateValue() != null || 
                (questionInput.getQuestion().isAskForTrust() && questionInput.validateTrust() != null);
      }
      else {
         return false;
      }
   }

   @Override
   public void reflow() {
      for (IQuestionInputManager manager : input2managerMap.values()) {
         if (manager instanceof IReflowParticipant) {
            ((IReflowParticipant) manager).reflow();
         }
      }
      super.reflow();
   }
}
