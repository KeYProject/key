package org.key_project.util.test.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

/**
 * Creates an empty perspective.
 * @author Martin Hentschel
 */
public class EmptyTestPerspectiveFactory implements IPerspectiveFactory {
   /**
    * The ID of this perspective.
    */
   public static final String PERSPECTIVE_ID = "org.key_project.util.test.perspective.EmptyTestPerspectiveFactory";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createInitialLayout(IPageLayout layout) {
   }
}
