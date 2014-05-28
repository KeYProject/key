package org.key_project.sed.core.model.event;

import java.util.EventObject;

import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * An event thrown by an {@link ISEDDebugNode} and observed via
 * {@link ISEDAnnotationLinkListener}.
 * @author Martin Hentschel
 */
public class SEDAnnotationLinkEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -4856346897532140703L;

   /**
    * The added or removed {@link ISEDAnnotationLink}.
    */
   private final ISEDAnnotationLink link;
   
   /**
    * Constructor.
    * @param source The modified {@link ISEDDebugNode}.
    * @param link The added or removed {@link ISEDAnnotationLink}.
    */
   public SEDAnnotationLinkEvent(ISEDDebugNode source, ISEDAnnotationLink link) {
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
   public ISEDDebugNode getSource() {
      return (ISEDDebugNode)super.getSource();
   }
}
