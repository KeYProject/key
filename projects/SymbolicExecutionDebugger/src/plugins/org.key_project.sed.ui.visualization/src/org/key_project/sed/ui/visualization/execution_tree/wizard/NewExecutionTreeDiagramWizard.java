package org.key_project.sed.ui.visualization.execution_tree.wizard;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.nio.charset.Charset;
import java.util.Collections;

import org.eclipse.core.resources.IFile;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.wizard.page.ContentWizardNewFileCreationPage;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * A new wizard to create Symbolic Execution Tree Diagrams.
 * @author Martin Hentschel
 */
public class NewExecutionTreeDiagramWizard extends BasicNewResourceWizard {
   /**
    * The contained {@link WizardNewFileCreationPage} which is used to define the diagram file.
    */
   private ContentWizardNewFileCreationPage diagramPage;

   /**
    * The contained {@link WizardNewFileCreationPage} which is used to define the model file.
    */
   private ContentWizardNewFileCreationPage modelPage;

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      super.addPages();
      setWindowTitle("Create Symbolic Execution Tree Diagram");
      diagramPage = new ContentWizardNewFileCreationPage("diagramPage", getSelection());
      diagramPage.setTitle("Create Symbolic Execution Tree Diagram");
      diagramPage.setDescription("Select file that will contain diagram model."); 
      diagramPage.setFileExtension(ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION);
      addPage(diagramPage);
      modelPage = new ContentWizardNewFileCreationPage("modelPage", getSelection());
      modelPage.setTitle("Create Symbolic Execution Tree Domain Model");
      modelPage.setDescription("Select file that will contain domain model."); 
      modelPage.setFileExtension(ExecutionTreeUtil.DOMAIN_FILE_EXTENSION);
      addPage(modelPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IWizardPage getNextPage(IWizardPage page) {
      IWizardPage next = super.getNextPage(page);
      if (next == modelPage) {
         updateModelPage();
      }
      return next;
   }

   /**
    * Updates {@link #modelPage} with default values.
    */
   protected void updateModelPage() {
      if (!ObjectUtil.equals(diagramPage.getContainerFullPath(), modelPage.getContainerFullPath())) {
         modelPage.setContainerFullPath(diagramPage.getContainerFullPath());
      }
      String domainFile = ExecutionTreeUtil.getInitialDomainFileName(diagramPage.getFileName());
      if (!ObjectUtil.equals(domainFile, modelPage.getFileName())) {
         modelPage.setFileName(domainFile);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         // Update domain wizard page if it is not currently shown
         if (!modelPage.isCurrentPage()) {
            updateModelPage();
         }
         // Create model file
         SEDXMLWriter writer = new SEDXMLWriter();
         String modelContent = writer.toXML(new IDebugTarget[0], "UTF-8");
         modelPage.setInitialContents(new ByteArrayInputStream(modelContent.getBytes(Charset.forName("UTF-8"))));
         IFile domainFile = modelPage.createNewFile();
         if (domainFile != null) {
            // Create diagram instance
            Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, 
                                                                          IOUtil.getFileNameWithoutExtension(diagramPage.getFileName()), 
                                                                          true);
            URI domainURI = URI.createPlatformResourceURI(domainFile.getFullPath().toString(), true);
            GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, domainURI.toString());
            // Save diagram
            ResourceSet rst = new ResourceSetImpl();
            Resource resource = rst.createResource(URI.createFileURI("invalid"));
            resource.getContents().add(diagram);
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            resource.save(out, Collections.EMPTY_MAP);
            diagramPage.setInitialContents(new ByteArrayInputStream(out.toByteArray()));
            IFile diagramFile = diagramPage.createNewFile();
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
