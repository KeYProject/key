package org.key_project.sed.core.annotation;

import java.util.Set;

import org.key_project.sed.core.annotation.event.ISEAnnotationLinkListener;
import org.key_project.sed.core.annotation.impl.AbstractSEAnnotation;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEIDElement;

/**
 * <p>
 * An annotation is of a single type ({@link #getType()}), 
 * may contain additional data (defined by the concrete implementations),
 * is added to {@link ISEDebugTarget}s and points via links 
 * ({@link ISEAnnotationLink}) to {@link ISENode}s contained in the 
 * subtree of the {@link ISEDebugTarget}.
 * </p>
 * <p>
 * Implementations should subclass from {@link AbstractSEAnnotation}.
 * </p>
 * <p>
 * Instances of this interface are created via 
 * {@link ISEAnnotationType#createAnnotation()}.
 * </p>
 * @author Martin Hentschel
 * @see ISEAnnotationType
 * @see ISEAnnotation
 */
public interface ISEAnnotation extends ISEAnnotationAppearance, ISEIDElement {
   /**
    * Property {@link #isEnabled()}.
    */
   public static final String PROP_ENABLED = "enabled";
   
   /**
    * Checks if the annotation is enabled.
    * @return {@code true} enabled, {@code false} disabled.
    */
   public boolean isEnabled();
   
   /**
    * Defines if the annotation is enabled.
    * @param enabled {@code true} enabled, {@code false} disabled.
    */
   public void setEnabled(boolean enabled);
   
   /**
    * Adds the given {@link ISEAnnotationLink}.
    * @param link The {@link ISEAnnotationLink} to add.
    */
   public void addLink(ISEAnnotationLink link);

   /**
    * Removes the given {@link ISEAnnotationLink}.
    * @param link The {@link ISEAnnotationLink} to remove.
    */
   public void removeLink(ISEAnnotationLink link);
   
   /**
    * Returns all contained {@link ISEAnnotationLink}s.
    * @return All contained {@link ISEAnnotationLink}s.
    */
   public ISEAnnotationLink[] getLinks();
   
   /**
    * Returns the {@link ISEAnnotationLink} at the given index.
    * @param index The index.
    * @return The found {@link ISEAnnotationLink} or {@code null} if not available.
    */
   public ISEAnnotationLink getLinkAt(int index);
   
   /**
    * Checks if the given {@link ISEAnnotationLink} is contained.
    * @param link The {@link ISEAnnotationLink} to check.
    * @return {@code true} {@link ISEAnnotationLink} is contained, {@code false} otherwise.
    */
   public boolean containsLink(ISEAnnotationLink link);
   
   /**
    * Checks if at least one link is available.
    * @return {@code false} no links available, {@code true} at least one link is available.
    */
   public boolean hasLinks();

   /**
    * Returns the number of contained links.
    * @return The number of contained links.
    */
   public int countLinks();

   /**
    * Returns the index of the given link.
    * @param link The link.
    * @return The index of the given link or {@code -1} if not contained.
    */
   public int indexOfLink(ISEAnnotationLink link);

   /**
    * Checks if this annotation can be deleted from the given {@link ISEDebugTarget}.
    * @param target The {@link ISEDebugTarget} to remove annotation from.
    * @return {@code true} can delete, {@code false} can not delete.
    */
   public boolean canDelete(ISEDebugTarget target);
   
   /**
    * Removes this annotation from the given {@link ISEDebugTarget}.
    * @param target The {@link ISEDebugTarget} to remove this annotation from.
    */
   public void delete(ISEDebugTarget target);
   
   /**
    * Adds the given {@link ISEAnnotationLinkListener}.
    * @param l The {@link ISEAnnotationLinkListener} to add.
    */
   public void addAnnotationLinkListener(ISEAnnotationLinkListener l);
   
   /**
    * Removes the given {@link ISEAnnotationLinkListener}.
    * @param l The {@link ISEAnnotationLinkListener} to remove.
    */
   public void removeAnnotationLinkListener(ISEAnnotationLinkListener l);

   /**
    * Lists all {@link ISENode}s which are targets of {@link #getLinks()}.
    * @return The {@link Set} with all available {@link ISENode}s.
    */
   public Set<ISENode> listLinkTargets();
   
   /**
    * Sets the unique ID which is valid as long as it was never accessed before.
    * @param id The new unique ID to use.
    */
   public void setId(String id);
}
