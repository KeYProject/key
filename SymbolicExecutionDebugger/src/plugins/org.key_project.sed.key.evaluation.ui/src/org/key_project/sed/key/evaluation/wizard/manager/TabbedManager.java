package org.key_project.sed.key.evaluation.wizard.manager;

import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.TabbedQuestion;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage.ICreateControlCallback;

public class TabbedManager extends AbstractQuestionInputManager {
   private final CTabFolder tabFolder;
   
   private final List<IQuestionInputManager> childManagers;
   
   public TabbedManager(AbstractEvaluationWizardPage<?> wizardPage,
                        FormToolkit toolkit, 
                        Composite parent, 
                        QuestionInput questionInput,
                        TabbedQuestion question,
                        ICreateControlCallback callback) {
      tabFolder = new CTabFolder(parent, SWT.NONE);
      toolkit.adapt(tabFolder);
      if (parent.getLayout() instanceof GridLayout) {
         tabFolder.setLayoutData(new GridData(GridData.FILL_BOTH));
      }
      childManagers = QuestionWizardPage.createQuestionControls(wizardPage, toolkit, tabFolder, questionInput.getChildInputs(), callback);
   }

   @Override
   public void dispose() {
      for (IQuestionInputManager manager : childManagers) {
         manager.dispose();
      }
   }

   @Override
   protected void enableControls(boolean enabled) {
      tabFolder.setEnabled(enabled);
      for (IQuestionInputManager manager : childManagers) {
         manager.setEnabled(enabled);
      }
   }

   @Override
   public Control getFocusControl() {
      return tabFolder;
   }
}
