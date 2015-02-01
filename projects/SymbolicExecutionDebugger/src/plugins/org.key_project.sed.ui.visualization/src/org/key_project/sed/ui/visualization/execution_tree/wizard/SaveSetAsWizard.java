package org.key_project.sed.ui.visualization.execution_tree.wizard;

import java.io.ByteArrayInputStream;
import java.lang.reflect.InvocationTargetException;
import java.nio.charset.Charset;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.execution_tree.wizard.page.ModelFileSaveOptionsWizardPage;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.swt.wizard.page.ContentWizardNewFileCreationPage;
import org.key_project.util.java.thread.AbstractRunnableWithProgressAndResult;
import org.key_project.util.java.thread.IRunnableWithProgressAndResult;

/**
 * This {@link Wizard} to save an {@link ILaunch} as SET file. 
 * @author Martin Hentschel
 */
public class SaveSetAsWizard extends BasicNewResourceWizard {
   /**
    * The currently active {@link IWorkbenchWindow}.
    */
   private final IWorkbenchWindow window;

   /**
    * The {@link ISEDDebugTarget}s to save.
    */
   private final ISEDDebugTarget[] targets;
   
   /**
    * The used {@link ContentWizardNewFileCreationPage}.
    */
   private ContentWizardNewFileCreationPage modelPage;
   
   /**
    * The used {@link ModelFileSaveOptionsWizardPage}.
    */
   private ModelFileSaveOptionsWizardPage optionsPage;

   /**
    * Constructor.
    * @param window The currently active {@link IWorkbenchWindow}.
    * @param targets The {@link ISEDDebugTarget}s to save.
    */
   public SaveSetAsWizard(IWorkbenchWindow window, ISEDDebugTarget[] targets) {
      Assert.isNotNull(targets);
      this.window = window;
      this.targets = targets;
      setWindowTitle("Save as");
      setNeedsProgressMonitor(true);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      modelPage = new ContentWizardNewFileCreationPage("modelPage", StructuredSelection.EMPTY);
      modelPage.setTitle("Save Symbolic Execution Tree");
      modelPage.setDescription("Select file that will contain the symbolic execution tree."); 
      modelPage.setFileExtension(ExecutionTreeUtil.DOMAIN_FILE_EXTENSION);
      addPage(modelPage);
      optionsPage = new ModelFileSaveOptionsWizardPage("optionsPage");
      addPage(optionsPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         final boolean saveVariables = optionsPage.isSaveVariables();
         final boolean saveCallStack = optionsPage.isSaveCallStack();
         final boolean saveConstraints = optionsPage.isSaveConstraints();
         IRunnableWithProgressAndResult<String> run = new AbstractRunnableWithProgressAndResult<String>() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               try {
                  SEDXMLWriter writer = new SEDXMLWriter();
                  String content = writer.toXML(targets, 
                                                SEDXMLWriter.DEFAULT_ENCODING, 
                                                saveVariables, 
                                                saveCallStack,
                                                saveConstraints,
                                                monitor);
                  setResult(content);
               }
               catch (OperationCanceledException e) {
                  // Nothing to do
               }
               catch (Exception e) {
                  throw new InvocationTargetException(e);
               }
            }
         };
         getContainer().run(true, true, run);
         if (run.getResult() != null) {
            modelPage.setInitialContents(new ByteArrayInputStream(run.getResult().getBytes(Charset.forName(SEDXMLWriter.DEFAULT_ENCODING))));
            IFile file = modelPage.createNewFile();
            if (window != null) {
               selectAndReveal(file, window);
            }
            return true;
         }
         else {
            return false;
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         return false;
      }
   }
   
   /**
    * Opens the {@link SaveSetAsWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param window The currently active {@link IWorkbenchWindow}.
    * @param targets The {@link ISEDDebugTarget}s to save.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, 
                                IWorkbenchWindow window,
                                ISEDDebugTarget[] targets) {
      WizardDialog dialog = new WizardDialog(parentShell, new SaveSetAsWizard(window, targets));
      return dialog.open();
   }
}
