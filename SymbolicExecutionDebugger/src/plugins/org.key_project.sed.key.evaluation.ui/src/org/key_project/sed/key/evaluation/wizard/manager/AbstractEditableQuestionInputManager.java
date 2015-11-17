package org.key_project.sed.key.evaluation.wizard.manager;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;

public abstract class AbstractEditableQuestionInputManager extends AbstractQuestionInputManager {
   private final AbstractEvaluationWizardPage<?> wizardPage;
      
   private final QuestionInput questionInput;
   
   private Section questionSection;
   
   private TrustManager trustManager;
   
   private final PropertyChangeListener questionListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleQuestionValueChanged(evt);
      }
   };

   public AbstractEditableQuestionInputManager(AbstractEvaluationWizardPage<?> wizardPage, QuestionInput questionInput) {
      this.wizardPage = wizardPage;
      this.questionInput = questionInput;
      questionInput.addPropertyChangeListener(QuestionInput.PROP_VALUE, questionListener);
   }
   
   protected void createSection(FormToolkit toolkit, Composite parent, AbstractQuestion question) {
      Composite sectionComposite = toolkit.createComposite(parent);
      TableWrapLayout sectionLayout = new TableWrapLayout();
      sectionLayout.numColumns = 2;
      sectionComposite.setLayout(sectionLayout);
      questionSection = toolkit.createSection(sectionComposite, SWT.WRAP);
      if (question.getLabel() != null) {
         questionSection.setText(question.getLabel());
      }
      if (question.getDescription() != null) {
         questionSection.setClient(toolkit.createLabel(questionSection, question.getDescription(), SWT.WRAP));
      }
      if (question.isAskForTrust()) {
         trustManager = new TrustManager(wizardPage, sectionComposite, getQuestionInput());
      }
   }

   protected Section getQuestionSection() {
      return questionSection;
   }

   protected abstract void handleQuestionValueChanged(PropertyChangeEvent evt);

   public QuestionInput getQuestionInput() {
      return questionInput;
   }
   
   public AbstractEvaluationWizardPage<?> getWizardPage() {
      return wizardPage;
   }
   
   @Override
   protected void enableControls(boolean enabled) {
      if (questionSection != null) {
         questionSection.setEnabled(enabled);
      }
      if (trustManager != null) {
         trustManager.setEnabled(enabled);
      }
   }

   @Override
   public void dispose() {
      questionInput.removePropertyChangeListener(QuestionInput.PROP_VALUE, questionListener);
      if (trustManager != null) {
         trustManager.dispose();
      }
   }

   @Override
   public Control getFocusControl() {
      return questionSection;
   }
}
