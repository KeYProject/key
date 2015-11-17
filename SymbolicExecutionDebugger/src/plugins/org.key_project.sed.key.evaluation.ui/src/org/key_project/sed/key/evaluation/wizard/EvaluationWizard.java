package org.key_project.sed.key.evaluation.wizard;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.key.evaluation.io.SendThread;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.InstructionPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.input.SendFormPageInput;
import org.key_project.sed.key.evaluation.model.input.ToolPageInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputWriter;
import org.key_project.sed.key.evaluation.util.LogUtil;
import org.key_project.sed.key.evaluation.wizard.dialog.EvaluationWizardDialog;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.InstructionWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.QuestionWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.SendFormWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.ToolWizardPage;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.thread.AbstractRunnableWithProgressAndResult;
import org.key_project.util.thread.IRunnableWithProgressAndResult;

public class EvaluationWizard extends Wizard {
   private final EvaluationInput evaluationInput;
   
   private AbstractEvaluationWizardPage<?> lastPage;
   
   private IWizardPage currentPage;
   
   private IRunnableWithProgressAndResult<String> currentPageRunnable;
   
   private final ImageDescriptor imageDescriptor;
   
   public EvaluationWizard(EvaluationInput evaluationInput, ImageDescriptor imageDescriptor) {
      assert evaluationInput != null;
      this.evaluationInput = evaluationInput;
      this.imageDescriptor = imageDescriptor;
      setNeedsProgressMonitor(true);
      setHelpAvailable(false);
      setWindowTitle(evaluationInput.getEvaluation().getName());
   }

   @Override
   public void addPages() {
      for (AbstractFormInput<?> form : evaluationInput.getFormInputs()) {
         for (AbstractPageInput<?> page : form.getPageInputs()) {
            if (page.getPage().isEnabled()) {
               if (page instanceof QuestionPageInput) {
                  lastPage = new QuestionWizardPage((QuestionPageInput) page, imageDescriptor);
               }
               else if (page instanceof SendFormPageInput) {
                  SendFormPageInput sendPage = (SendFormPageInput) page;
                  lastPage = new SendFormWizardPage(sendPage, evaluationInput.getFormInput(sendPage.getPage().getForm()), imageDescriptor);
               }
               else if (page instanceof ToolPageInput) {
                  lastPage = new ToolWizardPage((ToolPageInput) page, imageDescriptor);
               }
               else if (page instanceof InstructionPageInput) {
                  lastPage = new InstructionWizardPage((InstructionPageInput) page, imageDescriptor);
               }
               else {
                  throw new IllegalStateException("Unsupported page input: " + page);
               }
               addPage(lastPage);
            }
         }
      }
   }

   @Override
   public IWizardPage getStartingPage() {
      currentPage = getPage(evaluationInput.getCurrentFormInput().getCurrentPageInput());
      return currentPage;
   }

   @Override
   public IWizardPage getPreviousPage(IWizardPage page) {
      IWizardPage previousPage = computePreviousPage(page);
      if (previousPage != null) {
         AbstractForm currentForm = ((AbstractEvaluationWizardPage<?>) page).getPageInput().getPage().getForm();
         AbstractForm previousForm = ((AbstractEvaluationWizardPage<?>) previousPage).getPageInput().getPage().getForm();
         if (currentForm == previousForm) {
            return previousPage;
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
   
   protected IWizardPage computePreviousPage(IWizardPage page) {
      AbstractPageInput<?> pageInput = ((AbstractEvaluationWizardPage<?>) page).getPageInput();
      AbstractFormInput<?> formInput = pageInput.getFormInput();
      if (formInput instanceof RandomFormInput) {
         RandomFormInput randomInput = (RandomFormInput) formInput;
         if (!CollectionUtil.isEmpty(randomInput.getPageOrder())) {
            int pageOrderIndex = randomInput.getPageOrder().indexOf(pageInput);
            if (pageOrderIndex < 0) {
               // Should never happen
               throw new IllegalStateException("Current page not part of order!");
            }
            else if (pageOrderIndex - 1 >= 0) {
               // Previous random page
               return getPage(randomInput.getPageOrder().get(pageOrderIndex - 1));
            }
            else {
               // First page
               int formIndex = formInput.getEvaluationInput().indexOfFormInput(formInput);
               if (formIndex < 0) {
                  // Should never happen
                  throw new IllegalStateException("Current form is not part of evaluation!");
               }
               else if (formIndex - 1 >= 0) {
                  AbstractFormInput<?> previousForm = formInput.getEvaluationInput().getFormInput(formIndex - 1);
                  if (previousForm.countPageInputs() >= 1) {
                     return getLastRandomPage(getPage(previousForm.getPageInput(previousForm.countPageInputs() - 1)));
                  }
                  else {
                     return null; // No previous page exist
                  }
               }
               else {
                  return null; // No previous page exist
               }
            }
         }
         else {
            return getLastRandomPage(super.getPreviousPage(page));
         }
      }
      else {
         return getLastRandomPage(super.getPreviousPage(page));
      }
   }

   private IWizardPage getLastRandomPage(IWizardPage page) {
      if (page != null) {
         AbstractPageInput<?> pageInput = ((AbstractEvaluationWizardPage<?>) page).getPageInput();
         AbstractFormInput<?> formInput = pageInput.getFormInput();
         if (formInput instanceof RandomFormInput) {
            RandomFormInput randomInput = (RandomFormInput) formInput;
            if (!CollectionUtil.isEmpty(randomInput.getPageOrder())) {
               return getPage(randomInput.getPageOrder().get(randomInput.getPageOrder().size() - 1));
            }
            else {
               return page;
            }
         }
         else {
            return page;
         }
      }
      else {
         return null;
      }
   }

   @Override
   public IWizardPage getNextPage(IWizardPage page) {
      AbstractPageInput<?> pageInput = ((AbstractEvaluationWizardPage<?>) page).getPageInput();
      AbstractFormInput<?> formInput = pageInput.getFormInput();
      if (formInput instanceof RandomFormInput) {
         RandomFormInput randomInput = (RandomFormInput) formInput;
         if (!CollectionUtil.isEmpty(randomInput.getPageOrder())) {
            int pageOrderIndex = randomInput.getPageOrder().indexOf(pageInput);
            if (pageOrderIndex < 0) {
               // Should never happen
               throw new IllegalStateException("Current page not part of order!");
            }
            else if (pageOrderIndex + 1 < randomInput.getPageOrder().size()) {
               // Next random page
               return getPage(randomInput.getPageOrder().get(pageOrderIndex + 1));
            }
            else {
               // Last page
               int formIndex = formInput.getEvaluationInput().indexOfFormInput(formInput);
               if (formIndex < 0) {
                  // Should never happen
                  throw new IllegalStateException("Current form is not part of evaluation!");
               }
               else if (formIndex + 1 < formInput.getEvaluationInput().countFormInputs()) {
                  AbstractFormInput<?> nextForm = formInput.getEvaluationInput().getFormInput(formIndex + 1);
                  if (nextForm.countPageInputs() >= 1) {
                     return getFirstRandomPage(getPage(nextForm.getPageInput(0)));
                  }
                  else {
                     return null; // No next page exist
                  }
               }
               else {
                  return null; // No next page exist
               }
            }
         }
         else {
            return getFirstRandomPage(super.getNextPage(page));
         }
      }
      else {
         return getFirstRandomPage(super.getNextPage(page));
      }
   }

   private IWizardPage getFirstRandomPage(IWizardPage page) {
      if (page != null) {
         AbstractPageInput<?> pageInput = ((AbstractEvaluationWizardPage<?>) page).getPageInput();
         AbstractFormInput<?> formInput = pageInput.getFormInput();
         if (formInput instanceof RandomFormInput) {
            RandomFormInput randomInput = (RandomFormInput) formInput;
            if (!CollectionUtil.isEmpty(randomInput.getPageOrder())) {
               return getPage(randomInput.getPageOrder().get(0));
            }
            else {
               return page;
            }
         }
         else {
            return page;
         }
      }
      else {
         return null;
      }
   }

   public IWizardPage getPage(final AbstractPageInput<?> pageInput) {
      return ArrayUtil.search(getPages(), new IFilter<IWizardPage>() {
         @Override
         public boolean select(IWizardPage element) {
            return ((AbstractEvaluationWizardPage<?>) element).getPageInput() == pageInput;
         }
      });
   }

   public boolean nextPressed(AbstractEvaluationWizardPage<?> currentPage) {
      if (currentPage instanceof SendFormWizardPage) {
         SendFormWizardPage sendPage = (SendFormWizardPage) currentPage;
         AbstractFormInput<?> formInput = sendPage.getFormInput();
         return sendForm(sendPage.getPageInput(), formInput);
      }
      else {
         return true;
      }
   }

   @Override
   public boolean canFinish() {
      return lastPage == currentPage && super.canFinish();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      if (currentPage instanceof SendFormWizardPage) {
         SendFormWizardPage sendPage = (SendFormWizardPage) currentPage;
         AbstractFormInput<?> formInput = sendPage.getFormInput();
         return sendForm(sendPage.getPageInput(), formInput);
      }
      else {
         return true;
      }
   }
   
   public boolean sendForm(final SendFormPageInput sendInput, final AbstractFormInput<?> formInput) {
      try {
         sendInput.setSendingInProgress(true);
         IRunnableWithProgressAndResult<Boolean> run = new AbstractRunnableWithProgressAndResult<Boolean>() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               monitor.beginTask("Sending content", IProgressMonitor.UNKNOWN);
               setResult(Boolean.FALSE);
               SendThread sendThread = new SendThread(EvaluationInputWriter.toFormAnswerXML(formInput));
               sendThread.start();
               while (sendThread.isAlive() && !monitor.isCanceled()) {
                  Thread.sleep(100);
               }
               monitor.done();
               if (monitor.isCanceled()) {
                  sendThread.cancel();
               }
               else {
                  if (sendThread.getException() != null) {
                     throw new InvocationTargetException(sendThread.getException(), sendThread.getException().getMessage());
                  }
                  else {
                     EvaluationInput answerInput = sendThread.getAnswerInput();
                     // Check answer
                     if (answerInput == null) {
                        throw new InvocationTargetException(null, "No valid answer received.");
                     }
                     if (evaluationInput.getEvaluation() != answerInput.getEvaluation()) {
                        throw new InvocationTargetException(null, "Received answer does not fit with current evaluation.");
                     }
                     // Set or check UUID
                     SendThread.updateUUID(evaluationInput, answerInput);
                     // Update page orders
                     SendThread.updatePageOrder(evaluationInput, answerInput);
                     setResult(Boolean.TRUE);
                  }
               }
            }
         };
         getContainer().run(true, true, run);
         return run.getResult().booleanValue();
      }
      catch (OperationCanceledException e) {
         return false;
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         return false;
      }
      finally {
         sendInput.setSendingInProgress(false);
      }
   }

   public void setCurrentPage(IWizardPage currentPage) {
      this.currentPage = currentPage;
   }

   public IRunnableWithProgressAndResult<String> getCurrentPageRunnable() {
      return currentPageRunnable;
   }

   public void setCurrentPageRunnable(IRunnableWithProgressAndResult<String> currentPageRunnable) {
      this.currentPageRunnable = currentPageRunnable;
   }

   public ImageDescriptor getImageDescriptor() {
      return imageDescriptor;
   }

   /**
    * Opens the {@link EvaluationWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param alwaysOnTop {@code true} The wizard is always on top, {@code false} the wizard is not always on top.
    * @param evaluationInput The {@link EvaluationInput} to perform.
    */
   public static void openWizard(Shell parentShell, boolean alwaysOnTop, EvaluationInput evaluationInput, ImageDescriptor imageDescriptor, Image image) {
      try {
         EvaluationWizardDialog openedDialog = EvaluationWizardDialog.getFirstVisibleWizardDialog(evaluationInput);
         if (openedDialog != null) {
            openedDialog.getShell().setFocus();
         }
         else {
            boolean openWizard = true;
            // Check existing input
            if (evaluationInput.getCurrentFormInput() == evaluationInput.getFormInput(0)) {
               // Ensure that evaluation always start from beginning
               evaluationInput.reset();
            }
            else {
               // Ask to restart evaluation
               int result = SWTUtil.openMessageDialog(parentShell, 
                                                      "Continue Evaluation?", 
                                                      image,
                                                      "Continue the already started evaluation? (Recommended)", 
                                                      MessageDialog.QUESTION, 
                                                      new String[] {IDialogConstants.YES_LABEL, IDialogConstants.NO_LABEL});
               if (result == 1) {
                  int secondResult = SWTUtil.openMessageDialog(parentShell, 
                                                               "Continue Evaluation?", 
                                                               image,
                                                               "Please do only restart the evaluation if you have not participated before and if you have not seen parts of the evaluation.\n\nContinue the already started evaluation? (Recommended)", 
                                                               MessageDialog.WARNING, 
                                                               new String[] {IDialogConstants.YES_LABEL, IDialogConstants.NO_LABEL});
                  if (secondResult == 1) {
                     evaluationInput.reset();
                  }
                  else if (secondResult != 0) {
                     openWizard = false; // -1 if cancelled, e.g. ESC
                  }
               }
               else if (result != 0) { // -1 if cancelled, e.g. ESC
                  openWizard = false;
               }
            }
            // Open wizard
            if (openWizard) {
               EvaluationWizardDialog dialog = new EvaluationWizardDialog(parentShell, alwaysOnTop, evaluationInput, imageDescriptor, image);
               dialog.open();
            }
         }
      }
      catch (SWTError e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(parentShell, 
                                             "Error", 
                                             "Ensure that the internal Browser of Eclipse is available.\n"
                                             + "Installation of libwebkitgtk (sudo apt-get install libwebkitgtk-1.0-0) might help.", // See http://askubuntu.com/questions/220505/how-to-enable-the-eclipse-internal-browser-ubuntu-12-10
                                             e); 
      }
   }
}
