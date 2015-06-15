package org.key_project.sed.key.evaluation.wizard.dialog;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.net.URL;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import org.eclipse.jface.dialogs.DialogTray;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.TraverseEvent;
import org.eclipse.swt.events.TraverseListener;
import org.eclipse.swt.graphics.Cursor;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.InstructionPage;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.FixedFormInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.input.SendFormPageInput;
import org.key_project.sed.key.evaluation.model.tooling.IWorkbenchModifier;
import org.key_project.sed.key.evaluation.util.LogUtil;
import org.key_project.sed.key.evaluation.util.SEDEvaluationImages;
import org.key_project.sed.key.evaluation.wizard.EvaluationWizard;
import org.key_project.sed.key.evaluation.wizard.manager.BrowserManager;
import org.key_project.sed.key.evaluation.wizard.page.AbstractEvaluationWizardPage;
import org.key_project.sed.key.evaluation.wizard.page.SendFormWizardPage;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;

public class EvaluationWizardDialog extends WizardDialog {
   private static final Map<EvaluationInput, WeakHashMap<EvaluationWizardDialog, Void>> dialogInstances = new HashMap<EvaluationInput, WeakHashMap<EvaluationWizardDialog, Void>>();

   private final EvaluationInput evaluationInput;
   
   private final PropertyChangeListener currentPageListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleCurrentPageChanged(evt);
      }
   };

   private final PropertyChangeListener sendingListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleSendingInProgressChanged(evt);
      }
   };
   
   private boolean messageClickable = false;
   
   private Cursor handCursor;
   
   private ToolBar toolBar;
   
   private final boolean alwaysOnTop;
   
   private final MouseListener messageMouseListener = new MouseListener() {
      @Override
      public void mouseUp(MouseEvent e) {
         handleMessageClick(e);
      }
      
      @Override
      public void mouseDown(MouseEvent e) {
      }
      
      @Override
      public void mouseDoubleClick(MouseEvent e) {
         handleMessageClick(e);
      }
   };
   
   private final Shell originalParentShell;
   
   private EvaluationWizardDialog wizardToClose;
   
   private final Rectangle initialBounds;

   public EvaluationWizardDialog(Shell parentShell, boolean alwaysOnTop, EvaluationInput evaluationInput) {
      this(parentShell, alwaysOnTop, evaluationInput, null);
   }

   protected EvaluationWizardDialog(Shell parentShell, boolean alwaysOnTop, EvaluationInput evaluationInput, EvaluationWizardDialog wizardDialogToClose) {
      super(alwaysOnTop ? parentShell : null, new EvaluationWizard(evaluationInput));
      this.originalParentShell = parentShell;
      this.alwaysOnTop = alwaysOnTop;
      this.evaluationInput = evaluationInput;
      this.wizardToClose = wizardDialogToClose;
      if (wizardToClose != null) {
         initialBounds = wizardDialogToClose.getShell().getBounds();
      }
      else {
         initialBounds = null;
      }
      evaluationInput.getCurrentFormInput().addPropertyChangeListener(AbstractFormInput.PROP_CURRENT_PAGE_INPUT, currentPageListener);
      setHelpAvailable(false);
   }

   public EvaluationInput getEvaluationInput() {
      return evaluationInput;
   }

   @Override
   protected int getShellStyle() {
      return SWT.CLOSE | SWT.MAX | SWT.TITLE | SWT.BORDER | SWT.RESIZE | getDefaultOrientation();
   }

   @Override
   public void showPage(IWizardPage page) {
      if (getCurrentPage() instanceof SendFormWizardPage) {
         ((SendFormWizardPage) getCurrentPage()).getPageInput().removePropertyChangeListener(SendFormPageInput.PROP_SENDING_IN_PROGRESS, sendingListener);
      }
      getWizard().setCurrentPage(page);
      super.showPage(page);
      updateToolbar();
      assert page instanceof AbstractEvaluationWizardPage<?>;
      AbstractEvaluationWizardPage<?> evaluationPage = (AbstractEvaluationWizardPage<?>) page;
      evaluationInput.getCurrentFormInput().setCurrentPageInput(evaluationPage.getPageInput());
      if (page instanceof SendFormWizardPage) {
         ((SendFormWizardPage) page).getPageInput().addPropertyChangeListener(SendFormPageInput.PROP_SENDING_IN_PROGRESS, sendingListener);
      }
   }
   
   protected void updateToolbar() {
      // Dispose old items
      for (ToolItem item : toolBar.getItems()) {
         item.dispose();
      }
      // Create instruction items
      boolean separatorNeeded = false;
      AbstractEvaluationWizardPage<?> currentWizardPage = getCurrentPage();
      AbstractPageInput<?> pageInput = currentWizardPage.getPageInput();
      AbstractFormInput<?> formInput = pageInput.getFormInput();
      if (currentWizardPage != null) {
         AbstractForm form = formInput.getForm();
         for (AbstractPage page : form.getPages()) {
            if (page instanceof InstructionPage && wasShownBefore(pageInput, page)) {
               InstructionPage ip = (InstructionPage) page;
               createToolBarItem(ip.getImage(), ip.getTitle(), ip.getDescriptionURL());
               separatorNeeded = true;
            }
         }
      }
      // Create tool items
      Tool tool = formInput instanceof RandomFormInput ?
                  ((RandomFormInput) formInput).getTool(pageInput) :
                  null;
      if (tool != null) {
         createToolBarItem(tool.getImage(), tool.getName(), tool.getDescriptionURL());
         separatorNeeded = true;
      }
      // Create pin item
      if (separatorNeeded) {
         new ToolItem(toolBar, SWT.SEPARATOR);
      }
      ToolItem pinItem = new ToolItem(toolBar, SWT.CHECK);
      pinItem.setSelection(alwaysOnTop);
      pinItem.setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.PIN_SHELL));
      pinItem.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            togglePinnedState();
         }
      });
      pinItem.setToolTipText("Show wizard always on top?");
      // Layout toolbar
      toolBar.layout();
      toolBar.getParent().layout();
   }
   
   protected void togglePinnedState() {
      EvaluationWizardDialog dialog = new EvaluationWizardDialog(originalParentShell, !alwaysOnTop, evaluationInput, this);
      dialog.open();
   }

   protected boolean wasShownBefore(AbstractPageInput<?> currentPageInput, AbstractPage toCheck) {
      if (currentPageInput.getFormInput() instanceof FixedFormInput) {
         boolean before = false;
         boolean goOn = true;
         AbstractPage[] pages = currentPageInput.getFormInput().getForm().getPages();
         int i = 0;
         while (goOn && i < pages.length) {
            if (pages[i] == currentPageInput.getPage()) {
               goOn = false;
            }
            else if (pages[i] == toCheck) {
               before = true;
               goOn = false;
            }
            i++;
         }
         return before;
      }
      else if (currentPageInput.getFormInput() instanceof RandomFormInput) {
         boolean before = false;
         boolean goOn = true;
         List<AbstractPageInput<?>> pages = ((RandomFormInput) currentPageInput.getFormInput()).getPageOrder();
         Iterator<AbstractPageInput<?>> iter = pages.iterator();
         while (goOn && iter.hasNext()) {
            AbstractPage next = iter.next().getPage();
            if (next == currentPageInput.getPage()) {
               goOn = false;
            }
            else if (next == toCheck) {
               before = true;
               goOn = false;
            }
         }
         return before;
      }
      else {
         throw new IllegalStateException("Unsupported form input: " + currentPageInput.getFormInput());
      }
   }

   protected void createToolBarItem(final Image image, final String name, final URL url) {
      ToolItem item = new ToolItem(toolBar, SWT.PUSH);
      if (image != null) {
         item.setImage(image);
      }
      else {
         item.setText(name);
      }
      item.setToolTipText("Open instructions about " + name + " in a new shell.");
      item.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            openURL(image, name, url);
         }
      });
   }

   protected void openURL(Image image, String title, URL url) {
      final Shell shell = new Shell(getShell().getDisplay());
      if (title != null) {
         shell.setText(title);
      }
      shell.setImage(image);
      shell.addTraverseListener(new TraverseListener() {
         @Override
         public void keyTraversed(TraverseEvent e) {
            if (e.detail == SWT.TRAVERSE_ESCAPE) {
               shell.close();
            }
         }
      });
      shell.setLayout(new FillLayout());
      FormToolkit toolkit = new FormToolkit(shell.getDisplay());
      BrowserManager.createBrowser(toolkit, shell, url);
      shell.setSize(400, 400);
      SWTUtil.centerOn(getShell(), shell);
      shell.open();
   }

   @Override
   protected void nextPressed() {
      if (getWizard().nextPressed(getCurrentPage())) {
         super.nextPressed();
      }
   }

   @Override
   protected void finishPressed() {
      super.finishPressed();
      if (getReturnCode() == OK) {
         removeListener();
      }
   }

   @Override
   public AbstractEvaluationWizardPage<?> getCurrentPage() {
      return (AbstractEvaluationWizardPage<?>) super.getCurrentPage();
   }

   protected void handleCurrentPageChanged(PropertyChangeEvent evt) {
      if (evt.getNewValue() != getCurrentPage().getPageInput()) {
         IWizardPage newPage = getWizard().getPage((AbstractPageInput<?>)evt.getNewValue());
         assert newPage != null;
         showPage(newPage);
      }
   }

   protected void handleSendingInProgressChanged(PropertyChangeEvent evt) {
      boolean sendingInProgress = (Boolean)evt.getNewValue();
      if (sendingInProgress) {
         getButton(IDialogConstants.CANCEL_ID).setEnabled(false);
         getButton(IDialogConstants.FINISH_ID).setEnabled(false);
         getButton(IDialogConstants.NEXT_ID).setEnabled(false);
         getButton(IDialogConstants.BACK_ID).setEnabled(false);
      }
      else {
         getButton(IDialogConstants.CANCEL_ID).setEnabled(true);
         getButton(IDialogConstants.FINISH_ID).setEnabled(true);
         getButton(IDialogConstants.NEXT_ID).setEnabled(true);
         getButton(IDialogConstants.BACK_ID).setEnabled(true);
         updateButtons();
      }
   }

   @Override
   protected EvaluationWizard getWizard() {
      return (EvaluationWizard)super.getWizard();
   }

   @Override
   public void openTray(DialogTray tray) throws IllegalStateException,UnsupportedOperationException {
      registerDialog(this);
      super.openTray(tray);
   }

   @Override
   public void create() {
      super.create();
      // Ensure that a button is selected, otherwise radio buttons might change values
      if (!getButton(IDialogConstants.NEXT_ID).isEnabled()) {
         getButton(IDialogConstants.CANCEL_ID).forceFocus();
      }
      // Perform runnable of current page if available
      if (getWizard().getCurrentPageRunnable() != null) {
         getShell().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               getCurrentPage().perfomRunnables(null, getWizard().getCurrentPageRunnable());
               getWizard().setCurrentPageRunnable(null);
            }
         });
      }
   }
   
   @Override
   protected Control createContents(Composite parent) {
      getShell().setImage(SEDEvaluationImages.getImage(SEDEvaluationImages.EVALUATION));
      handCursor = new Cursor(getShell().getDisplay(), SWT.CURSOR_HAND);
      Control control = super.createContents(parent);
      updateToolbar();
      return control;
   }

   @Override
   protected Control createButtonBar(Composite parent) {
      Composite composite = new Composite(parent, SWT.NONE);
      GridLayout layout = new GridLayout(2, false);
      layout.marginWidth = 0;
      layout.marginHeight = 0;
      layout.horizontalSpacing = 0;
      composite.setLayout(layout);
      composite.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false));
      composite.setFont(parent.getFont());
      // Create additional buttons
      toolBar = new ToolBar(composite, SWT.FLAT | SWT.NO_FOCUS);
      toolBar.setLayoutData(new GridData(GridData.HORIZONTAL_ALIGN_CENTER));
      ((GridData) toolBar.getLayoutData()).horizontalIndent = convertHorizontalDLUsToPixels(IDialogConstants.HORIZONTAL_MARGIN);
      
      // Create original buttons
      Control buttonSection = super.createButtonBar(composite);
      ((GridData) buttonSection.getLayoutData()).grabExcessHorizontalSpace = true;
      return composite;
   }

   protected Rectangle getConstrainedShellBounds(Rectangle preferredSize) {
      if (initialBounds != null && !getShell().isVisible()) {
         return initialBounds;
      }
      else {
         Rectangle result = super.getConstrainedShellBounds(preferredSize);
         if (result.width > 600) {
            result.width = 600;
         }
         if (result.height > 700) {
            result.height = 700;
         }
         return result;
      }
   }

   @Override
   public int open() {
      registerDialog(this);
      if (wizardToClose != null) {
         wizardToClose.close();
         wizardToClose = null;
      }
      return super.open();
   }

   @Override
   public boolean close() {
      boolean closed = super.close();
      if (closed) {
         handCursor.dispose();
         unregisterDialog(this);
         removeListener();
         try {
            if (!hasDialogs(evaluationInput)) {
               AbstractPage currentPage = getCurrentPage().getPageInput().getPage();
               if (currentPage instanceof QuestionPage) {
                  IWorkbenchModifier modifier = ((QuestionPage) currentPage).getWorkbenchModifier();
                  if (modifier != null) {
                     modifier.cleanWorkbench();
                  }
               }
            }
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
         }
      }
      return closed;
   }
   
   protected void removeListener() {
      if (getCurrentPage() instanceof SendFormWizardPage) {
         ((SendFormWizardPage) getCurrentPage()).getPageInput().removePropertyChangeListener(SendFormPageInput.PROP_SENDING_IN_PROGRESS, sendingListener);
      }
      evaluationInput.getCurrentFormInput().removePropertyChangeListener(AbstractFormInput.PROP_CURRENT_PAGE_INPUT, currentPageListener);
   }

   public static void registerDialog(EvaluationWizardDialog dialog) {
      synchronized (dialogInstances) {
         WeakHashMap<EvaluationWizardDialog, Void> evaluationMap = dialogInstances.get(dialog.getEvaluationInput());
         if (evaluationMap == null) {
            evaluationMap = new WeakHashMap<EvaluationWizardDialog, Void>();
            dialogInstances.put(dialog.getEvaluationInput(), evaluationMap);
         }
         evaluationMap.put(dialog, null);
      }
   }

   public static void unregisterDialog(EvaluationWizardDialog dialog) {
      synchronized (dialogInstances) {
         WeakHashMap<EvaluationWizardDialog, Void> evaluationMap = dialogInstances.get(dialog.getEvaluationInput());
         if (evaluationMap == null) {
            evaluationMap = new WeakHashMap<EvaluationWizardDialog, Void>();
            dialogInstances.put(dialog.getEvaluationInput(), evaluationMap);
         }
         evaluationMap.remove(dialog);
      }
   }
   
   public static boolean hasDialogs(EvaluationInput evaluationInput) {
      synchronized (dialogInstances) {
         WeakHashMap<EvaluationWizardDialog, Void> evaluationMap = dialogInstances.get(evaluationInput);
         if (evaluationMap != null) {
            return !evaluationMap.isEmpty();
         }
         else {
            return false;
         }
      }
   }
   
   @Override
   public void updateMessage() {
      super.updateMessage();
      boolean newClickable = getCurrentPage() != null && getCurrentPage().isMessageClickable();
      if (newClickable != messageClickable) {
         Control messageLabel = getMessageLabel();
         Control messageImageLabel = getMessageImageLabel();
         if (newClickable) {
            messageLabel.setCursor(handCursor);
            messageLabel.setForeground(getShell().getDisplay().getSystemColor(SWT.COLOR_LINK_FOREGROUND));
            messageLabel.addMouseListener(messageMouseListener);
            messageImageLabel.setCursor(handCursor);
            messageImageLabel.addMouseListener(messageMouseListener);
         }
         else {
            messageLabel.setCursor(null);
            messageLabel.setForeground(null);
            messageLabel.removeMouseListener(messageMouseListener);
            messageImageLabel.setCursor(null);
            messageImageLabel.removeMouseListener(messageMouseListener);
         }
         messageClickable = newClickable;
      }
   }

   protected void handleMessageClick(MouseEvent e) {
      if (getCurrentPage() != null) {
         getCurrentPage().performMessageClick();
      }
   }

   protected Control getMessageLabel() {
      try {
         return (Control) ObjectUtil.get(this, "messageLabel");
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         return null;
      }
   }
   
   protected Control getMessageImageLabel() {
      try {
         return (Control) ObjectUtil.get(this, "messageImageLabel");
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         return null;
      }
   }
}
