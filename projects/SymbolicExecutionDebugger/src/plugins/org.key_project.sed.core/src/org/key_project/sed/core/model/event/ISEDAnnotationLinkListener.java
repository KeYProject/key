package org.key_project.sed.core.model.event;

import java.util.EventListener;

import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Listens for changes on an {@link ISEDDebugNode}.
 * @author Martin Hentschel
 */
public interface ISEDAnnotationLinkListener extends EventListener {
   /**
    * When a new {@link ISEDAnnotationLink} was added via
    * {@link ISEDDebugNode#addAnnotationLink(ISEDAnnotationLink)}.
    * @param e The event.
    */
   public void annotationLinkAdded(SEDAnnotationLinkEvent e);

   /**
    * When an existing {@link ISEDAnnotationLink} was removed via
    * {@link ISEDDebugNode#removeAnnotationLink(ISEDAnnotationLink)}.
    * @param e The event.
    */
   public void annotationLinkRemoved(SEDAnnotationLinkEvent e);
}
