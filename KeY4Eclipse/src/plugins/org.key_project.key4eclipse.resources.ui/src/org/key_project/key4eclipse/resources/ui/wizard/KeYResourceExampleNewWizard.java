package org.key_project.key4eclipse.resources.ui.wizard;

import java.io.IOException;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.ui.wizards.NewJavaProjectWizardPageOne;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildJob;
import org.key_project.key4eclipse.resources.ui.Activator;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * {@link Wizard} to create a new KeY project filled with some example content.
 * @author Martin Hentschel
 */
public class KeYResourceExampleNewWizard extends KeYProjectWizard {
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      super.addPages();
      // Set initial project name.
      for (IWizardPage page : getPages()) {
         if (page instanceof NewJavaProjectWizardPageOne) {
            final NewJavaProjectWizardPageOne one = (NewJavaProjectWizardPageOne)page;
            Display.getDefault().asyncExec(new Runnable() {
               @Override
               public void run() {
                  one.setProjectName("KeY Project Example");
               }
            });
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeWindowTitle() {
      return "New KeY Project filled with example content";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeDescription() {
      return "Create a KeY project in the workspace or in an external location filled with example content.";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeTitle() {
      return "Create a KeY Project filled with example content";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         // Create KeY project
         boolean done = super.performFinish();
         if (done) {
            // Get source code directory
            IResource sourceDirectory = getSourceDirectory();
            // Check if a source code directory was found
            if (sourceDirectory instanceof IContainer) {
               waitBuild();
               done = createExampleContent((IContainer)sourceDirectory);
            }
         }
         return done;
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }
   
   //TODO refactor out
   public static void waitBuild() {
      IJobManager manager = Job.getJobManager();
      // Wait for jobs and builds.
      Job[] keyJobs = manager.find(KeYProjectBuildJob.KEY_PROJECT_BUILD_JOB);
      Job[] buildJobs = manager.find(ResourcesPlugin.FAMILY_AUTO_BUILD);
      while (!ArrayUtil.isEmpty(keyJobs) || !ArrayUtil.isEmpty(buildJobs)) {
         // Sleep some time but allow the UI to do its tasks
         if (Display.getDefault().getThread() == Thread.currentThread()) {
            int i = 0;
            while (Display.getDefault().readAndDispatch() && i < 1000) {
               i++;
            }
         }
         else {
            try {
               Thread.sleep(100);
            }
            catch (InterruptedException e) {
               // TODO Auto-generated catch block
               e.printStackTrace();
            }
         }
         // Check if jobs are still running
         keyJobs = manager.find(KeYProjectBuildJob.KEY_PROJECT_BUILD_JOB);
         buildJobs = manager.find(ResourcesPlugin.FAMILY_AUTO_BUILD);
      }
   }

   /**
    * Adds the example content to the given source directory.
    * @param sourceDirectory The given source directory.
    * @return {@code true} = close wizard, {@code false} = keep wizard opened.
    * @throws Exception Occurred Exception.
    */
   @SuppressWarnings("restriction")
   protected boolean createExampleContent(final IContainer sourceDirectory) throws Exception {
      ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {
          @Override
          public void run(IProgressMonitor monitor) throws CoreException {
              try {
                  // Add source code
                  BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/exampleProject/src", sourceDirectory);
                  IFile multipleRecursionFile = sourceDirectory.getFile(new Path("MultipleRecursion.java"));
                  // Add proofs
                  IFolder fileFolder = KeYResourcesUtil.getProofFolder(multipleRecursionFile);
                  IFile aProof = KeYResourcesUtil.getProofFile("MultipleRecursion[MultipleRecursion::b()].JML normal_behavior operation contract.0", fileFolder.getFullPath());
                  IFile bProof = KeYResourcesUtil.getProofFile("MultipleRecursion[MultipleRecursion::a()].JML normal_behavior operation contract.0", fileFolder.getFullPath());
                  if (!fileFolder.exists()) {
                     KeYResourcesUtil.createFolder(aProof);
                  }
                  BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/exampleProject/proofs/a.proof", aProof);
                  BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/exampleProject/proofs/b.proof", bProof);
              }
              catch (IOException e) {
                  throw new CoreException(LogUtil.getLogger().createErrorStatus(e.getMessage(), e));
              }
          }
      }, null);
      // Open first example file
      IFile integerUtilFile = sourceDirectory.getFile(new Path("IntegerUtil.java"));
      if (integerUtilFile != null && integerUtilFile.exists()) {
         selectAndReveal(integerUtilFile);
         WorkbenchUtil.openEditor(integerUtilFile);
      }
      return true;
   }
}
