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

package org.key_project.sed.ui.perspective;

import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

/**
 * Creates the symbolic debug perspective.
 * @author Martin Hentschel
 */
public class SymbolicDebugPerspectiveFactory implements IPerspectiveFactory {
   /**
    * The ID of this perspective.
    */
   public static final String PERSPECTIVE_ID = "org.key_project.sed.ui.perspective";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createInitialLayout(IPageLayout layout) {
      // Get the editor area.
      String editorArea = layout.getEditorArea();
      // Put the debug view on the left.
      IFolderLayout leftFolder = layout.createFolder("left", IPageLayout.LEFT, 0.5f, editorArea);
      leftFolder.addView(IDebugUIConstants.ID_DEBUG_VIEW);
      // Put the properties view on bottom left.
      IFolderLayout bottomLeftFolder = layout.createFolder("bottomLeft", IPageLayout.BOTTOM, 0.8f, "left");
      bottomLeftFolder.addView(IPageLayout.ID_PROP_SHEET);
      // Put the variables view on top.
      IFolderLayout topFolder = layout.createFolder("top", IPageLayout.TOP, 0.2f, editorArea);
      topFolder.addView(IDebugUIConstants.ID_VARIABLE_VIEW);
      topFolder.addView(IDebugUIConstants.ID_BREAKPOINT_VIEW);
      // Perspective Shortcuts
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaPerspective");
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaHierarchyPerspective");
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaBrowsingPerspective");
      layout.addPerspectiveShortcut("org.eclipse.debug.ui.DebugPerspective");
      // View Shortcuts
      layout.addShowViewShortcut(IDebugUIConstants.ID_DEBUG_VIEW);
      layout.addShowViewShortcut(IDebugUIConstants.ID_VARIABLE_VIEW);
      layout.addShowViewShortcut(IDebugUIConstants.ID_BREAKPOINT_VIEW);
      layout.addShowViewShortcut(IPageLayout.ID_PROP_SHEET);
   }
}