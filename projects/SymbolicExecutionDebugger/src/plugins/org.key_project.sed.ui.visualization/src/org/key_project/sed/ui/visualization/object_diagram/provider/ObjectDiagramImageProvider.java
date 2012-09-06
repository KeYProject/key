package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.eclipse.graphiti.ui.platform.AbstractImageProvider;
import org.eclipse.graphiti.ui.platform.IImageProvider;

/**
 * <p>
 * {@link IImageProvider} specific implementation for object diagrams.
 * </p>
 * <p>
 * The constants of provided images are specified via interface {@link IObjectDiagramImageConstants}.
 * </p>
 * <p>
 * This class is instantiated an managed by Graphiti's extension points.
 * </p>
 * @author Martin Hentschel
 * @see IObjectDiagramImageConstants
 */
public class ObjectDiagramImageProvider extends AbstractImageProvider {
   /**
    * Path to the folder which contains the provided images.
    */
   private static final String ROOT_FOLDER_FOR_IMG = "icons/";

   /**
    * {@inheritDoc}
    */
   @Override
   protected void addAvailableImages() {
       addImageFilePath(IObjectDiagramImageConstants.IMG_OBJECT, ROOT_FOLDER_FOR_IMG + "object.gif");
       addImageFilePath(IObjectDiagramImageConstants.IMG_ASSOCIATION, ROOT_FOLDER_FOR_IMG + "association.gif");
   }
}