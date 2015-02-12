/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.ui.visualization.execution_tree.wizard;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.nio.charset.Charset;
import java.util.Collections;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.transaction.RecordingCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.execution_tree.wizard.page.ModelFileSaveOptionsWizardPage;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.wizard.page.ContentWizardNewFileCreationPage;
import org.key_project.util.java.ObjectUtil;

/**
 * A {@link BasicNewResourceWizard} which is used to define a diagram and model file.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionTreeDiagramSaveAsWizard extends BasicNewResourceWizard {
   /**
    * The contained {@link WizardNewFileCreationPage} which is used to define the diagram file.
    */
   private ContentWizardNewFileCreationPage diagramPage;

   /**
    * The contained {@link WizardNewFileCreationPage} which is used to define the model file.
    */
   private ContentWizardNewFileCreationPage modelPage;
   
   /**
    * The optionally contained {@link ModelFileSaveOptionsWizardPage}.
    */
   private ModelFileSaveOptionsWizardPage optionsPage;

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      super.addPages();
      setWindowTitle(getInitialWindowTitle());
      diagramPage = new ContentWizardNewFileCreationPage("diagramPage", getSelection());
      diagramPage.setTitle(getDiagramPageTitle());
      diagramPage.setDescription("Select file that will contain diagram model."); 
      diagramPage.setFileExtension(ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION);
      addPage(diagramPage);
      modelPage = new ContentWizardNewFileCreationPage("modelPage", getSelection());
      modelPage.setTitle(getModelPageTitle());
      modelPage.setDescription("Select file that will contain domain model."); 
      modelPage.setFileExtension(ExecutionTreeUtil.DOMAIN_FILE_EXTENSION);
      addPage(modelPage);
      optionsPage = createModelFileSaveOptionsWizardPage("optionsPage");
      if (optionsPage != null) {
         addPage(optionsPage);
      }
   }
   
   /**
    * Creates the {@link ModelFileSaveOptionsWizardPage} if it should be used.
    * @param pageName The page name to use.
    * @return The {@link ModelFileSaveOptionsWizardPage} to use or {@code null} otherwise.
    */
   protected ModelFileSaveOptionsWizardPage createModelFileSaveOptionsWizardPage(String pageName) {
      return null;
   }
   
   /**
    * Returns the initial window title to use.
    * @return The initial window title to use.
    */
   protected abstract String getInitialWindowTitle();
   
   /**
    * Returns the title of wizard page to define the diagram file.
    * @return The title.
    */
   protected abstract String getDiagramPageTitle();

   /**
    * Returns the title of wizard page to define the model file.
    * @return The title.
    */
   protected abstract String getModelPageTitle();
   
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
         if (!getModelPage().isCurrentPage()) {
            updateModelPage();
         }
         // Get debug targets
         ISEDDebugTarget[] targets = getDebugTargetsToSave();
         // Create model file
         SEDXMLWriter writer = new SEDXMLWriter();
         String modelContent = writer.toXML(targets, 
                                            "UTF-8", 
                                            optionsPage != null && optionsPage.isSaveVariables(), 
                                            optionsPage != null && optionsPage.isSaveCallStack(),
                                            optionsPage != null && optionsPage.isSaveConstraints(),
                                            null);
         getModelPage().setInitialContents(new ByteArrayInputStream(modelContent.getBytes(Charset.forName("UTF-8"))));
         IFile domainFile = getModelPage().createNewFile();
         if (domainFile != null) {
            // Get diagram
            final Diagram diagram = getDiagramToSave();
            Assert.isTrue(diagram.eResource() == null, "Diagram to save is already contained in a Resource.");
            TransactionalEditingDomain domain = ExecutionTreeUtil.createDomainAndResource(diagram); 
            final URI domainURI = URI.createPlatformResourceURI(domainFile.getFullPath().toString(), true);
            domain.getCommandStack().execute(new RecordingCommand(domain, "Set link to model file.") {
               @Override
               protected void doExecute() {
                  GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, domainURI.toString());
               }

               @Override
               public boolean canUndo() {
                  return false;
               }
            });
            // Save diagram
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            Resource resource = diagram.eResource();
            resource.save(out, Collections.EMPTY_MAP);
            getDiagramPage().setInitialContents(new ByteArrayInputStream(out.toByteArray()));
            IFile diagramFile = getDiagramPage().createNewFile();
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

   /**
    * Returns the {@link ISEDDebugTarget}s to save.
    * @return The {@link ISEDDebugTarget}s to save.
    */
   protected abstract ISEDDebugTarget[] getDebugTargetsToSave();

   /**
    * Returns the {@link Diagram} to save.
    * @return The {@link Diagram} to save.
    */
   protected abstract Diagram getDiagramToSave();

   /**
    * Returns the {@link ContentWizardNewFileCreationPage} used for selection of diagram file.
    * @return The {@link ContentWizardNewFileCreationPage} used for selection of diagram file.
    */
   protected ContentWizardNewFileCreationPage getDiagramPage() {
      return diagramPage;
   }

   /**
    * Returns the {@link ContentWizardNewFileCreationPage} used for selection of model file.
    * @return The {@link ContentWizardNewFileCreationPage} used for selection of model file.
    */
   protected ContentWizardNewFileCreationPage getModelPage() {
      return modelPage;
   }
}