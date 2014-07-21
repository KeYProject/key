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

package org.key_project.sed.ui.visualization.object_diagram.perspective;

import org.eclipse.graphiti.ui.internal.editor.ThumbNailView;
import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;

/**
 * Creates the state visualization perspective.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class StateVisualizationPerspectiveFactory implements IPerspectiveFactory {
   /**
    * The ID of this perspective.
    */
   public static final String PERSPECTIVE_ID = "org.key_project.sed.ui.visualization.stateVisualizationPerspective";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createInitialLayout(IPageLayout layout) {
      // Get the editor area.
      String editorArea = layout.getEditorArea();
      // Put the properties view on bottom left.
      IFolderLayout bottomLeftFolder = layout.createFolder("bottomLeft", IPageLayout.BOTTOM, 0.8f, editorArea);
      bottomLeftFolder.addView(IPageLayout.ID_PROP_SHEET);
      IFolderLayout bottomRightFolder = layout.createFolder("bottomRight", IPageLayout.RIGHT, 0.8f, "bottomLeft");
      bottomRightFolder.addView(ThumbNailView.VIEW_ID);
      // Perspective Shortcuts
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaPerspective");
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaHierarchyPerspective");
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaBrowsingPerspective");
      layout.addPerspectiveShortcut("org.eclipse.debug.ui.DebugPerspective");
      layout.addPerspectiveShortcut(SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID);
      // View Shortcuts
      layout.addShowViewShortcut(IPageLayout.ID_PROP_SHEET);
      layout.addShowViewShortcut(ThumbNailView.VIEW_ID);
   }
}