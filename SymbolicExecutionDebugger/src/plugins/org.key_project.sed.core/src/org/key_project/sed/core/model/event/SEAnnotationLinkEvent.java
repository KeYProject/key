package org.key_project.sed.core.model.event;

import java.util.EventObject;

import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISENode;

/**
 * An event thrown by an {@link ISENode} and observed via
 * {@link ISEAnnotationLinkListener}.
 * @author Martin Hentschel
 */
public class SEAnnotationLinkEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -4856346897532140703L;

   /**
    * The added or removed {@link ISEAnnotationLink}.
    */
   private final ISEAnnotationLink link;
   
   /**
    * Constructor.
    * @param source The modified {@link ISENode}.
    * @param link The added or removed {@link ISEAnnotationLink}.
    */
   public SEAnnotationLinkEvent(ISENode source, ISEAnnotationLink link) {
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
   public ISENode getSource() {
      return (ISENode)super.getSource();
   }
}
