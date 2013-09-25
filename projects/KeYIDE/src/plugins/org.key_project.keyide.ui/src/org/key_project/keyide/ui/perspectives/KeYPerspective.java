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

package org.key_project.keyide.ui.perspectives;

import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.key_project.keyide.ui.views.StrategySettingsView;

import de.uka.ilkd.key.proof.Proof;

/**
 * This class defines the layout of the KeY-View.
 * This view should be used whenever a {@link Proof} is started or a KeY-associated file is opened.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class KeYPerspective implements IPerspectiveFactory {
   /**
    * The ID of this perspective.
    */
   public static final String PERSPECTIVE_ID = "org.key_project.keyide.ui.perspectives";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createInitialLayout(IPageLayout layout) {
      // Get the editor area.
      String editorArea = layout.getEditorArea();
      // Put the debug view on the left.
      IFolderLayout leftFolder = layout.createFolder("left", IPageLayout.LEFT, 0.2f, editorArea);
      leftFolder.addView(JavaUI.ID_PACKAGES);
      // Put the properties view on bottom left.
      IFolderLayout bottomLeftFolder = layout.createFolder("bottomLeft", IPageLayout.BOTTOM, 0.75f, "left");
      bottomLeftFolder.addView(StrategySettingsView.VIEW_ID);
      // Put the out line on the right.
      IFolderLayout rightFolder = layout.createFolder("right", IPageLayout.RIGHT, 0.8f, editorArea);
      rightFolder.addView(IPageLayout.ID_OUTLINE);
      // Put the properties view on the bottom
      IFolderLayout bottomFolder = layout.createFolder("bottom", IPageLayout.BOTTOM, 0.75f, editorArea);
      bottomFolder.addView(IPageLayout.ID_PROP_SHEET);
      bottomFolder.addView(IPageLayout.ID_PROBLEM_VIEW);
      // Perspective Shortcuts
      layout.addPerspectiveShortcut(JavaUI.ID_PERSPECTIVE);
      layout.addPerspectiveShortcut(JavaUI.ID_HIERARCHYPERSPECTIVE);
      layout.addPerspectiveShortcut(JavaUI.ID_BROWSING_PERSPECTIVE);
      // View Shortcuts
      layout.addShowViewShortcut(StrategySettingsView.VIEW_ID);
      layout.addShowViewShortcut(IPageLayout.ID_PROP_SHEET);
      layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
      layout.addShowViewShortcut(IPageLayout.ID_PROBLEM_VIEW);
      layout.addShowViewShortcut(JavaUI.ID_PACKAGES);
   }
}