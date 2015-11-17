package org.key_project.sed.key.evaluation.wizard.manager;

import java.util.List;

import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.key_project.sed.key.evaluation.model.definition.SectionQuestion;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage.ICreateControlCallback;

public class SectionManager extends AbstractQuestionInputManager {
   private final Section section;
   
   private final List<IQuestionInputManager> childManagers;
   
   public SectionManager(AbstractEvaluationWizardPage<?> wizardPage,
                         FormToolkit toolkit, 
                         Composite parent, 
                         QuestionInput questionInput,
                         SectionQuestion question,
                         ICreateControlCallback callback) {
      section = toolkit.createSection(parent, Section.TITLE_BAR | Section.EXPANDED);
      if (parent.getLayout() instanceof GridLayout) {
         if (question.isGrapVerticalSpace()) {
            section.setLayoutData(new GridData(GridData.FILL_BOTH));
         }
         else {
            section.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         }
      }
      section.setText(question.getLabel());
      Composite sectionClient = toolkit.createComposite(section);
      sectionClient.setLayout(new GridLayout(1, false));
      childManagers = QuestionWizardPage.createQuestionControls(wizardPage, toolkit, sectionClient, questionInput.getChildInputs(), callback);
      section.setClient(sectionClient);
   }

   @Override
   public void dispose() {
      for (IQuestionInputManager manager : childManagers) {
         manager.dispose();
      }
   }

   @Override
   protected void enableControls(boolean enabled) {
      section.setEnabled(enabled);
      for (IQuestionInputManager manager : childManagers) {
         manager.setEnabled(enabled);
      }
   }

   @Override
   public Control getFocusControl() {
      return section;
   }
}
