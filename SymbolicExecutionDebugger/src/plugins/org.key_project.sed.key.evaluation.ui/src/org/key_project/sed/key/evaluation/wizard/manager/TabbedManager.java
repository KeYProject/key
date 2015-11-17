package org.key_project.sed.key.evaluation.wizard.manager;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.IPageWithWorkbenchModifier;
import org.key_project.sed.key.evaluation.model.definition.TabbedQuestion;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.tooling.IWorkbenchModifier;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage.ICreateControlCallback;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public class TabbedManager extends AbstractQuestionInputManager {
   private final CTabFolder tabFolder;
   
   private final List<IQuestionInputManager> childManagers;
   
   private final QuestionInput questionInput;
   
   private final AbstractEvaluationWizardPage<?> wizardPage;
   
   private final PropertyChangeListener questionListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleQuestionValueChanged();
      }
   };
   
   public TabbedManager(AbstractEvaluationWizardPage<?> wizardPage,
                        FormToolkit toolkit, 
                        Composite parent, 
                        QuestionInput questionInput,
                        TabbedQuestion question,
                        ICreateControlCallback callback) {
      this.questionInput = questionInput;
      this.wizardPage = wizardPage;
      tabFolder = new CTabFolder(parent, SWT.NONE);
      tabFolder.setData(this);
      tabFolder.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleSelectedTabChanged();
         }
      });
      toolkit.adapt(tabFolder);
      if (parent.getLayout() instanceof GridLayout) {
         tabFolder.setLayoutData(new GridData(GridData.FILL_BOTH));
      }
      childManagers = QuestionWizardPage.createQuestionControls(wizardPage, toolkit, tabFolder, questionInput.getChildInputs(), callback);
      questionInput.addPropertyChangeListener(QuestionInput.PROP_VALUE, questionListener);
      handleQuestionValueChanged();
      // Inform modifier about the initial state
      updateWorkbenchModifier();
   }

   @Override
   public void dispose() {
      questionInput.removePropertyChangeListener(QuestionInput.PROP_VALUE, questionListener);
      for (IQuestionInputManager manager : childManagers) {
         manager.dispose();
      }
   }

   public void handleSelectedTabChanged() {
      questionInput.setValue(tabFolder.getSelection().getText());
   }

   protected void handleQuestionValueChanged() {
      // Change UI selection
      CTabItem tabItem = ArrayUtil.search(tabFolder.getItems(), new IFilter<CTabItem>() {
         @Override
         public boolean select(CTabItem element) {
            return ObjectUtil.equals(element.getText(), questionInput.getValue());
         }
      });
      if (tabItem != null) {
         tabFolder.setSelection(tabItem);
      }
      // Inform modifier about the change
      updateWorkbenchModifier();
   }
   
   protected void updateWorkbenchModifier() {
      if (wizardPage.getPageInput().getPage() instanceof IPageWithWorkbenchModifier) {
         IPageWithWorkbenchModifier page = (IPageWithWorkbenchModifier) wizardPage.getPageInput().getPage();
         IWorkbenchModifier modifier = page.getWorkbenchModifier();
         if (modifier != null) {
            modifier.selectedTabChanged(questionInput);
         }
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
