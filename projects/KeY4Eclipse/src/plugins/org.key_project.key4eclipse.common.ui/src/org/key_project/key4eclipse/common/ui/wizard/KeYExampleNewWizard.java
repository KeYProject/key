package org.key_project.key4eclipse.common.ui.wizard;

import java.io.File;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;
import org.key_project.key4eclipse.common.ui.wizard.page.KeYExampleWizardPage;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.gui.ExampleChooser;

/**
 * The "KeY Example" wizard used to create new Java Projects with example
 * content provided by the KeY project.
 * @author Martin Hentschel
 */
public class KeYExampleNewWizard extends AbstractNewJavaProjectWizard {
   /**
    * The used {@link KeYExampleWizardPage} in which the user selects one example.
    */
   private KeYExampleWizardPage examplePage;

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getExampleName() {
      return "KeY Example";
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   public void addPages() {
      examplePage = new KeYExampleWizardPage("examplePage");
      addPage(examplePage);
      super.addPages();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canFinish() {
      return super.canFinish() && !examplePage.isCurrentPage();
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   protected boolean createExampleContent(IContainer sourceDirectory) throws Exception {
      // List example content
      File example = examplePage.getSelectedExample().getFile();
      File[] exampleContent = example.listFiles();
      // Copy example content into new created Java Project
      IProject project = sourceDirectory.getProject();
      ResourceUtil.copyIntoWorkspace(project, exampleContent);
      // Select project file
      IFile projectFile = project.getFile(new Path(ExampleChooser.KEY_FILE_NAME));
      if (projectFile.exists()) {
         selectAndReveal(projectFile);
      }
      return true;
   }
}
