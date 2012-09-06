package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODObject;

/**
 * <p>
 * This interface provides predefined image constants which can be used by the
 * features for image graphics algorithm.
 * </p>
 * <p>
 * Images itself are provided via {@link ObjectDiagramImageProvider} which
 * is instantiated and managed by Graphiti's extension points.
 * </p>
 * @author Martin Hentschel
 * @see ObjectDiagramImageProvider
 */
public interface IObjectDiagramImageConstants {
   /**
    * The constant prefix of all image keys.
    */
   public static final String PREFIX = "org.key_project.sed.ui.visualization.";
   
   /**
    * Key of the image for {@link ODObject}s.
    */
   public static final String IMG_OBJECT = PREFIX + "object";

   /**
    * Key of the image for {@link ODAssociation}s.
    */
   public static final String IMG_ASSOCIATION = PREFIX + "association";
}
