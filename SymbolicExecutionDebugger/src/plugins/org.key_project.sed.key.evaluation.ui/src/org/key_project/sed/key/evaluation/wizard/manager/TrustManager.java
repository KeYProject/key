package org.key_project.sed.key.evaluation.wizard.manager;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.util.SEDEvaluationImages;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;

public class TrustManager extends AbstractQuestionInputManager {
   private final AbstractEvaluationWizardPage<?> wizardPage;
   
   private final QuestionInput questionInput;
   
   private final PropertyChangeListener questionInputListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleQuestionTrustChange(evt);
      }
   };
   
   private ToolItem trustItem;
   
   private ToolItem dontTrustItem;
   
   public TrustManager(AbstractEvaluationWizardPage<?> wizardPage,
                       Composite parent, 
                       QuestionInput questionInput) {
      this.wizardPage = wizardPage;
      this.questionInput = questionInput;
      this.questionInput.addPropertyChangeListener(QuestionInput.PROP_TRUST, questionInputListener);
      ToolBar toolBar = new ToolBar(parent, SWT.FLAT | SWT.NO_FOCUS);
      toolBar.setBackground(parent.getBackground());
      trustItem = new ToolItem(toolBar, SWT.CHECK);
      trustItem.setSelection(questionInput.getTrust() != null && questionInput.getTrust().booleanValue());
      trustItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_FANTASY_DREAMING));
      trustItem.setToolTipText("I'm sure my answer is right!");
      trustItem.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleTrustItemSelectionChanged();
         }
      });
      dontTrustItem = new ToolItem(toolBar, SWT.CHECK);
      dontTrustItem.setSelection(questionInput.getTrust() != null && !questionInput.getTrust().booleanValue());
      dontTrustItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_OMG));
      dontTrustItem.setToolTipText("I'm unsure about my answer, it is probably wrong.");
      dontTrustItem.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleDontTrustItemSelectionChanged();
         }
      });
   }

   protected void handleTrustItemSelectionChanged() {
      dontTrustItem.setSelection(false);
      if (trustItem.getSelection()) {
         questionInput.setTrust(Boolean.TRUE);
         updateTrustSetAt();
      }
      else {
         questionInput.setTrust(null);
      }
   }
   
   protected void handleDontTrustItemSelectionChanged() {
      trustItem.setSelection(false);
      if (dontTrustItem.getSelection()) {
         questionInput.setTrust(Boolean.FALSE);
         updateTrustSetAt();
      }
      else {
         questionInput.setTrust(null);
      }
   }

   protected void updateTrustSetAt() {
      if (!questionInput.getPageInput().getPage().isReadonly() &&
          questionInput.getPageInput().getFormInput().getForm().isCollectTimes()) {
         long previousTimes = questionInput.getPageInput().getShownTime();
         long pageShownAt = wizardPage.getShownAt();
         long now = System.currentTimeMillis();
         questionInput.setTrustSetAt(previousTimes + (now - pageShownAt));
      }
   }

   protected void handleQuestionTrustChange(PropertyChangeEvent evt) {
      if (questionInput.getTrust() == null) {
         trustItem.setSelection(false);
         dontTrustItem.setSelection(false);
      }
      else {
         trustItem.setSelection(questionInput.getTrust());
         dontTrustItem.setSelection(!questionInput.getTrust());
      }
   }
   
   @Override
   public void dispose() {
      questionInput.removePropertyChangeListener(QuestionInput.PROP_TRUST, questionInputListener);
   }

   @Override
   protected void enableControls(boolean enabled) {
      if (trustItem != null) {
         trustItem.setEnabled(enabled);
      }
      if (dontTrustItem != null) {
         dontTrustItem.setEnabled(enabled);
      }
   }

   @Override
   public Control getFocusControl() {
      return trustItem.getParent();
   }
}
