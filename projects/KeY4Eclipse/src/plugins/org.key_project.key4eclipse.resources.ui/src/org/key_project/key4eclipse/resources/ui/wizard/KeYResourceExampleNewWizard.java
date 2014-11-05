package org.key_project.key4eclipse.resources.ui.wizard;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.ui.wizards.NewJavaProjectWizardPageOne;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.resources.ui.Activator;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

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

   /**
    * Adds the example content to the given source directory.
    * @param sourceDirectory The given source directory.
    * @return {@code true} = close wizard, {@code false} = keep wizard opened.
    * @throws Exception Occurred Exception.
    */
   @SuppressWarnings("restriction")
   protected boolean createExampleContent(IContainer sourceDirectory) throws Exception {
      // Add source code
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/exampleProject/src", sourceDirectory);
      IFile integerUtilFile = sourceDirectory.getFile(new Path("IntegerUtil.java"));
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
      // Open first example file
      if (integerUtilFile != null && integerUtilFile.exists()) {
         selectAndReveal(integerUtilFile);
         WorkbenchUtil.openEditor(integerUtilFile);
      }
      return true;
   }
}
