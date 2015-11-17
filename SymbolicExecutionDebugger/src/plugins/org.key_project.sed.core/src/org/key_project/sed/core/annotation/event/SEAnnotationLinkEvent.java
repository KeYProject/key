package org.key_project.sed.core.annotation.event;

import java.util.EventObject;

import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;

/**
 * An event thrown by an {@link ISEAnnotation} and observed via
 * {@link ISEAnnotationLinkListener}.
 * @author Martin Hentschel
 */
public class SEAnnotationLinkEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -678234884772978780L;

   /**
    * The added or removed {@link ISEAnnotationLink}.
    */
   private final ISEAnnotationLink link;
   
   /**
    * Constructor.
    * @param source The modified {@link ISEAnnotation}.
    * @param link The added or removed {@link ISEAnnotationLink}.
    */
   public SEAnnotationLinkEvent(ISEAnnotation source, ISEAnnotationLink link) {
      super(source);
      this.link = link;
   }

   /**
    * Returns the added or removed {@link ISEAnnotationLink}.
    * @return The added or removed {@link ISEAnnotationLink}.
    */
   public ISEAnnotationLink getLink() {
      return link;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotation getSource() {
      return (ISEAnnotation)super.getSource();
   }
}
