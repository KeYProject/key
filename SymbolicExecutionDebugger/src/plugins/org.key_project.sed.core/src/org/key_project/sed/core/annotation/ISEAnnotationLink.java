package org.key_project.sed.core.annotation;

import org.key_project.sed.core.annotation.impl.AbstractSEAnnotation;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEIDElement;
import org.key_project.util.bean.IBean;

/**
 * <p>
 * An annotation link is used by {@link ISEAnnotation}s to point to
 * {@link ISENode}s. It may provide additional data defined by
 * the interface implementation.
 * </p>
 * <p>
 * Implementations should subclass from {@link AbstractSEAnnotation}.
 * </p>
 * <p>
 * Instances of this interface are created via 
 * {@link ISEAnnotationType#createLink(ISEAnnotation, ISENode)}.
 * </p>
 * @author Martin Hentschel
 * @see ISEAnnotation
 * @see ISEAnnotationType
 */
public interface ISEAnnotationLink extends IBean, ISEIDElement {
   /**
    * Property {@link #getSource()}.
    */
   public static final String PROP_SOURCE = "source";
   
   /**
    * Property {@link #getTarget()}.
    */
   public static final String PROP_TARGET = "target";
   
   /**
    * Returns the source {@link ISEAnnotation}.
    * @return The source {@link ISEAnnotation}.
    */
   public ISEAnnotation getSource();
   
   /**
    * Returns the target {@link ISENode}.
    * @return The target {@link ISENode}.
    */
   public ISENode getTarget();
   
   /**
    * Checks if this annotation link can be deleted from the target {@link ISENode}.
    * @return {@code true} can delete, {@code false} can not delete.
    */
   public boolean canDelete();
   
   /**
    * Removes this annotation link form the target {@link ISENode}.
    */
   public void delete();

   /**
    * Sets the unique ID which is valid as long as it was never accessed before.
    * @param id The new unique ID to use.
    */
   public void setId(String id);
}
