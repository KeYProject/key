package org.key_project.stubby.ui.wizard;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.ui.util.LogUtil;
import org.key_project.stubby.ui.wizard.page.GenerateStubsWizardPage;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Stub generation {@link Wizard}.
 * @author Martin Hentschel
 */
public class GenerateStubsWizard extends Wizard {
   /**
    * The {@link IJavaProject} to generate stubs for.
    */
   private final IJavaProject javaProject;

   /**
    * The shown {@link GenerateStubsWizardPage}.
    */
   private final GenerateStubsWizardPage generatePage;
   
   /**
    * Constructor
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    */
   public GenerateStubsWizard(IJavaProject javaProject) {
      this.javaProject = javaProject;
      this.generatePage = new GenerateStubsWizardPage("generatePage", javaProject);
      setWindowTitle("Generate Stubs");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      addPage(generatePage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         final String stubFolderPath = generatePage.getStubFolderPath();
         getContainer().run(true, false, new IRunnableWithProgress() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               try {
                  StubGeneratorUtil.setStubFolderPath(javaProject, stubFolderPath);
                  StubGeneratorUtil.generateStubs(javaProject, stubFolderPath, monitor);
               }
               catch (CoreException e) {
                  throw new InvocationTargetException(e);
               }
            }
         });
         WorkbenchUtil.selectAndReveal(javaProject.getProject().getFolder(new Path(stubFolderPath)));
         return true;
      }
      catch (OperationCanceledException e) {
         return true;
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         return false;
      }
   }
   
   /**
    * Opens the {@link GenerateStubsWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param target The {@link IJavaProject} to generate stubs for.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, IJavaProject javaProject) {
      WizardDialog dialog = new WizardDialog(parentShell, new GenerateStubsWizard(javaProject));
      dialog.setHelpAvailable(false);
      return dialog.open();
   }
}
