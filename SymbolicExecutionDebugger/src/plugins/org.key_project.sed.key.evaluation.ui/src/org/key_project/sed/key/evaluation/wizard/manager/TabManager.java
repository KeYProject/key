package org.key_project.sed.key.evaluation.wizard.manager;

import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.key_project.sed.key.evaluation.model.definition.TabQuestion;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage.ICreateControlCallback;

public class TabManager extends AbstractQuestionInputManager implements IReflowParticipant {
   private final CTabItem tabItem;
   
   private final ScrolledComposite tabContent;
   
   private final List<IQuestionInputManager> childManagers;
   
   public TabManager(AbstractEvaluationWizardPage<?> wizardPage,
                     FormToolkit toolkit, 
                     Composite parent, 
                     QuestionInput questionInput,
                     TabQuestion question,
                     ICreateControlCallback callback) {
      CTabFolder tabFolder = (CTabFolder) parent;
      tabItem = new CTabItem(tabFolder, SWT.H_SCROLL | SWT.V_SCROLL);
      tabContent = new ScrolledComposite(parent, SWT.H_SCROLL | SWT.V_SCROLL);
      tabContent.setExpandHorizontal(true);
      tabContent.setExpandVertical(true);
      tabContent.setLayout(new FillLayout());
      Composite content = toolkit.createComposite(tabContent);
      content.setLayout(new TableWrapLayout());
      tabItem.setText(question.getLabel());
      childManagers = QuestionWizardPage.createQuestionControls(wizardPage, toolkit, content, questionInput.getChildInputs(), callback);
      tabContent.setContent(content);
      tabItem.setControl(tabContent);
      reflow();
      if (tabFolder.getSelection() == null) {
         tabFolder.setSelection(tabItem);
      }
   }

   @Override
   public void dispose() {
      for (IQuestionInputManager manager : childManagers) {
         manager.dispose();
      }
   }

   @Override
   protected void enableControls(boolean enabled) {
      for (IQuestionInputManager manager : childManagers) {
         manager.setEnabled(enabled);
      }
   }

   @Override
   public Control getFocusControl() {
      return tabContent;
   }

   @Override
   public void reflow() {
      tabContent.layout(true, true);
      tabContent.setMinSize(tabContent.getContent().computeSize(SWT.DEFAULT, SWT.DEFAULT));
   }
}
