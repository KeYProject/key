package org.key_project.sed.core.annotation.event;

import java.util.EventObject;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;

/**
 * An event thrown by an {@link ISEDAnnotation} and observed via
 * {@link ISEDAnnotationLinkListener}.
 * @author Martin Hentschel
 */
public class SEDAnnotationLinkEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -678234884772978780L;

   /**
    * The added or removed {@link ISEDAnnotationLink}.
    */
   private final ISEDAnnotationLink link;
   
   /**
    * Constructor.
    * @param source The modified {@link ISEDAnnotation}.
    * @param link The added or removed {@link ISEDAnnotationLink}.
    */
   public SEDAnnotationLinkEvent(ISEDAnnotation source, ISEDAnnotationLink link) {
      super(source);
      this.link = link;
   }

   /**
    * Returns the added or removed {@link ISEDAnnotationLink}.
    * @return The added or removed {@link ISEDAnnotationLink}.
    */
   public ISEDAnnotationLink getLink() {
      return link;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotation getSource() {
      return (ISEDAnnotation)super.getSource();
   }
}
