package org.key_project.sed.core.annotation;

import org.key_project.sed.core.annotation.impl.AbstractSEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDIDElement;
import org.key_project.util.bean.IBean;

/**
 * <p>
 * An annotation link is used by {@link ISEDAnnotation}s to point to
 * {@link ISEDDebugNode}s. It may provide additional data defined by
 * the interface implementation.
 * </p>
 * <p>
 * Implementations should subclass from {@link AbstractSEDAnnotation}.
 * </p>
 * <p>
 * Instances of this interface are created via 
 * {@link ISEDAnnotationType#createLink(ISEDAnnotation, ISEDDebugNode)}.
 * </p>
 * @author Martin Hentschel
 * @see ISEDAnnotation
 * @see ISEDAnnotationType
 */
public interface ISEDAnnotationLink extends IBean, ISEDIDElement {
   /**
    * Property {@link #getSource()}.
    */
   public static final String PROP_SOURCE = "source";
   
   /**
    * Property {@link #getTarget()}.
    */
   public static final String PROP_TARGET = "target";
   
   /**
    * Returns the source {@link ISEDAnnotation}.
    * @return The source {@link ISEDAnnotation}.
    */
   public ISEDAnnotation getSource();
   
   /**
    * Returns the target {@link ISEDDebugNode}.
    * @return The target {@link ISEDDebugNode}.
    */
   public ISEDDebugNode getTarget();
   
   /**
    * Checks if this annotation link can be deleted from the target {@link ISEDDebugNode}.
    * @return {@code true} can delete, {@code false} can not delete.
    */
   public boolean canDelete();
   
   /**
    * Removes this annotation link form the target {@link ISEDDebugNode}.
    */
   public void delete();

   /**
    * Sets the unique ID which is valid as long as it was never accessed before.
    * @param id The new unique ID to use.
    */
   public void setId(String id);
}
