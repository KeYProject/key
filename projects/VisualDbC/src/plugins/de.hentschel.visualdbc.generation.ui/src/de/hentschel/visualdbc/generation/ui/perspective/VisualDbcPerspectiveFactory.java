/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package de.hentschel.visualdbc.generation.ui.perspective;

import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.navigator.resources.ProjectExplorer;

/**
 * Creates the Visual DbC perspective.
 * @author Martin Hentschel
 */
public class VisualDbcPerspectiveFactory implements IPerspectiveFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public void createInitialLayout(IPageLayout layout) {
      // Get the editor area.
      String editorArea = layout.getEditorArea();
      // Put the Resource Explorer on the left.
      IFolderLayout topLeftFolder = layout.createFolder("topLeft", IPageLayout.LEFT, 0.25f, editorArea);
      topLeftFolder.addView(ProjectExplorer.VIEW_ID);
      // Put the outline in the bottom left area.
      IFolderLayout bottomLeftFolder = layout.createFolder("bottomLeft", IPageLayout.BOTTOM, 0.5f, "topLeft");
      bottomLeftFolder.addView(IPageLayout.ID_OUTLINE);
      // Put the log view on the bottom
      IFolderLayout bottomFolder = layout.createFolder("bottom", IPageLayout.BOTTOM, 0.75f, editorArea);
      bottomFolder.addView(IPageLayout.ID_PROP_SHEET);
//      bottomFolder.addView("org.eclipse.pde.runtime.LogView");
      bottomFolder.addPlaceholder(IPageLayout.ID_PROBLEM_VIEW);
      bottomFolder.addPlaceholder(IPageLayout.ID_BOOKMARKS);
//      bottomFolder.addPlaceholder(IPageLayout.ID_NAVIGATE_ACTION_SET);
      bottomFolder.addPlaceholder(IPageLayout.ID_PROGRESS_VIEW);
      bottomFolder.addPlaceholder(IPageLayout.ID_TASK_LIST);
      // Wizard Shortcuts
      layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.folder");
      layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.file");
      layout.addNewWizardShortcut("de.hentschel.visualdbc.dbcmodel.presentation.DbcmodelModelWizardID");
      layout.addNewWizardShortcut("de.hentschel.visualdbc.dbcmodel.diagram.part.DbcModelCreationWizardID");
      layout.addNewWizardShortcut("de.hentschel.visualdbc.generation.ui.wizard.GenerateDiagramWizard");
      // View Shortcuts
      layout.addShowViewShortcut(IPageLayout.ID_PROP_SHEET);
      layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
//      layout.addShowViewShortcut("org.eclipse.pde.runtime.LogView");
      layout.addShowViewShortcut(ProjectExplorer.VIEW_ID);
      // Perspective Shortcuts
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaPerspective");
      layout.addPerspectiveShortcut("org.eclipse.ui.resourcePerspective");
   }
}