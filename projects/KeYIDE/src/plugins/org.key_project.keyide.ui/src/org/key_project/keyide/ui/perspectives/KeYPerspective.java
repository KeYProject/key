package org.key_project.keyide.ui.perspectives;

import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;


/**
 *  This class is meant to serve as an example for how various contributions 
 *  are made to a perspective. Note that some of the extension point id's are
 *  referred to as API constants while others are hardcoded and may be subject 
 *  to change. 
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
      leftFolder.addView(IPageLayout.ID_PROJECT_EXPLORER);
      // Put the properties view on bottom left.
      IFolderLayout bottomLeftFolder = layout.createFolder("bottomLeft", IPageLayout.BOTTOM, 0.8f, "left");
      bottomLeftFolder.addView(IPageLayout.ID_PROP_SHEET);
      // Put the out line on the right.
      IFolderLayout rightFolder = layout.createFolder("right", IPageLayout.RIGHT, 0.8f, editorArea);
      rightFolder.addView(IPageLayout.ID_OUTLINE);
      // Perspective Shortcuts
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaPerspective");
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaHierarchyPerspective");
      layout.addPerspectiveShortcut("org.eclipse.jdt.ui.JavaBrowsingPerspective");
      layout.addPerspectiveShortcut("org.eclipse.debug.ui.DebugPerspective");
      // View Shortcuts
      layout.addShowViewShortcut(IPageLayout.ID_PROP_SHEET);
      layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
   }

}
