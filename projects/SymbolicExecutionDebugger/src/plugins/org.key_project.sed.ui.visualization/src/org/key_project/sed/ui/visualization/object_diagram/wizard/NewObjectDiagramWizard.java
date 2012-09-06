package org.key_project.sed.ui.visualization.object_diagram.wizard;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.util.Collections;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.object_diagram.provider.ObjectDiagramTypeProvider;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.wizard.page.ContentWizardNewFileCreationPage;
import org.key_project.util.java.IOUtil;

/**
 * A new wizard to create Object Diagrams.
 * @author Martin Hentschel
 */
public class NewObjectDiagramWizard extends BasicNewResourceWizard {
   /**
    * The contained {@link WizardNewFileCreationPage} which is used to define the diagram file.
    */
   private ContentWizardNewFileCreationPage diagramAndModelPage;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      super.addPages();
      setWindowTitle("Create Object Diagram");
      diagramAndModelPage = new ContentWizardNewFileCreationPage("diagramPage", getSelection());
      diagramAndModelPage.setTitle("Create Object Diagram");
      diagramAndModelPage.setDescription("Select file that will contain diagram and model."); 
      diagramAndModelPage.setFileExtension(ObjectDiagramUtil.DIAGRAM_AND_MODEL_FILE_EXTENSION);
      addPage(diagramAndModelPage);
   }
  
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         // Create empty diagram
         Diagram diagram = Graphiti.getPeCreateService().createDiagram(ObjectDiagramTypeProvider.TYPE, 
                                                                       IOUtil.getFileNameWithoutExtension(diagramAndModelPage.getFileName()), 
                                                                       true);
         Assert.isTrue(diagram.eResource() == null, "Diagram to save is already contained in a Resource.");
         ExecutionTreeUtil.createDomainAndResource(diagram); // Create Resource for the Diagram 
         // Save diagram
         ByteArrayOutputStream out = new ByteArrayOutputStream();
         Resource resource = diagram.eResource();
         resource.save(out, Collections.EMPTY_MAP);
         diagramAndModelPage.setInitialContents(new ByteArrayInputStream(out.toByteArray()));
         IFile diagramFile = diagramAndModelPage.createNewFile();
         if (diagramFile != null) {
            // Select and reveal file
            selectAndReveal(diagramFile);
            // Open diagram file
            WorkbenchUtil.openEditor(diagramFile);
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
}
