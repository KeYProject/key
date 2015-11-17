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
import org.key_project.sed.key.evaluation.model.input.Trust;
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
   
   private ToolItem sureItem;
   
   private ToolItem educatedGuessItem;
   
   private ToolItem unsureItem;
   
   public TrustManager(AbstractEvaluationWizardPage<?> wizardPage,
                       Composite parent, 
                       QuestionInput questionInput) {
      this.wizardPage = wizardPage;
      this.questionInput = questionInput;
      this.questionInput.addPropertyChangeListener(QuestionInput.PROP_TRUST, questionInputListener);
      ToolBar toolBar = new ToolBar(parent, SWT.FLAT | SWT.NO_FOCUS);
      toolBar.setBackground(parent.getBackground());
      sureItem = new ToolItem(toolBar, SWT.CHECK);
      sureItem.setSelection(Trust.SURE.equals(questionInput.getTrust()));
      sureItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_FANTASY_DREAMING));
      sureItem.setToolTipText("Sure: My answer is correct!");
      sureItem.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleSureItemSelectionChanged();
         }
      });
      educatedGuessItem = new ToolItem(toolBar, SWT.CHECK);
      educatedGuessItem.setSelection(Trust.EDUCATED_GUESS.equals(questionInput.getTrust()));
      educatedGuessItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_WOW_DUDE));
      educatedGuessItem.setToolTipText("Educated Guess: As far as I understood the content, my answer should be correct!");
      educatedGuessItem.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleEducatedGuessItemSelectionChanged();
         }
      });
      unsureItem = new ToolItem(toolBar, SWT.CHECK);
      unsureItem.setSelection(Trust.UNSURE.equals(questionInput.getTrust()));
      unsureItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_OMG));
      unsureItem.setToolTipText("Unsure: I tried my best, but I don't believe that my answer is correct.");
      unsureItem.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleUnsureItemSelectionChanged();
         }
      });
      updateIcons();
   }

   protected void updateIcons() {
      if (questionInput.getTrust() != null) {
         sureItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_FANTASY_DREAMING));
         educatedGuessItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_WOW_DUDE));
         unsureItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_OMG));
      }
      else {
         sureItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_FANTASY_DREAMING_ERROR));
         educatedGuessItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_WOW_DUDE_ERROR));
         unsureItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EMOTICON_OMG_ERROR));
      }
   }

   protected void handleEducatedGuessItemSelectionChanged() {
      sureItem.setSelection(false);
      unsureItem.setSelection(false);
      if (educatedGuessItem.getSelection()) {
         questionInput.setTrust(Trust.EDUCATED_GUESS);
         updateTrustSetAt();
      }
      else {
         questionInput.setTrust(null);
      }
   }

   protected void handleSureItemSelectionChanged() {
      unsureItem.setSelection(false);
      educatedGuessItem.setSelection(false);
      if (sureItem.getSelection()) {
         questionInput.setTrust(Trust.SURE);
         updateTrustSetAt();
      }
      else {
         questionInput.setTrust(null);
      }
   }
   
   protected void handleUnsureItemSelectionChanged() {
      sureItem.setSelection(false);
      educatedGuessItem.setSelection(false);
      if (unsureItem.getSelection()) {
         questionInput.setTrust(Trust.UNSURE);
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
         sureItem.setSelection(false);
         educatedGuessItem.setSelection(false);
         unsureItem.setSelection(false);
      }
      else {
         sureItem.setSelection(Trust.SURE.equals(questionInput.getTrust()));
         educatedGuessItem.setSelection(Trust.EDUCATED_GUESS.equals(questionInput.getTrust()));
         unsureItem.setSelection(Trust.UNSURE.equals(questionInput.getTrust()));
      }
      updateIcons();
   }
   
   @Override
   public void dispose() {
      questionInput.removePropertyChangeListener(QuestionInput.PROP_TRUST, questionInputListener);
   }

   @Override
   protected void enableControls(boolean enabled) {
      if (sureItem != null) {
         sureItem.setEnabled(enabled);
      }
      if (unsureItem != null) {
         unsureItem.setEnabled(enabled);
      }
   }

   @Override
   public Control getFocusControl() {
      return sureItem.getParent();
   }
}
