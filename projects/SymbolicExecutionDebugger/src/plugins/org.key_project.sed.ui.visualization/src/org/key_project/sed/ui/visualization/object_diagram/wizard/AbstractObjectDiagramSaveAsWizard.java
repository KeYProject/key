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

package org.key_project.sed.ui.visualization.object_diagram.wizard;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.util.Collections;

import org.eclipse.core.resources.IFile;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.wizard.page.ContentWizardNewFileCreationPage;

/**
 * A {@link BasicNewResourceWizard} which is used to define a diagram file which also includes the model.
 * @author Martin Hentschel
 */
public abstract class AbstractObjectDiagramSaveAsWizard extends BasicNewResourceWizard {
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
      setWindowTitle(getInitialWindowTitle());
      diagramAndModelPage = new ContentWizardNewFileCreationPage("diagramPage", getSelection());
      diagramAndModelPage.setTitle(getDiagramAndModelPageTitle());
      diagramAndModelPage.setDescription("Select file that will contain diagram and model."); 
      diagramAndModelPage.setFileExtension(ObjectDiagramUtil.DIAGRAM_AND_MODEL_FILE_EXTENSION);
      addPage(diagramAndModelPage);
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
   protected abstract String getDiagramAndModelPageTitle();
  
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         // Get diagram to save
         Diagram diagram = getDiagramToSave(diagramAndModelPage.getFileName());
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
   
   /**
    * Returns the {@link Diagram} to save.
    * @param fileName The defined file name by the user.
    * @return The {@link Diagram} to save.
    */
   protected abstract Diagram getDiagramToSave(String fileName);
}