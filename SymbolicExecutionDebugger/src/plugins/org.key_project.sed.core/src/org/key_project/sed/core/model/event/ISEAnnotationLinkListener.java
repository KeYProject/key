package org.key_project.sed.core.model.event;

import java.util.EventListener;

import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISENode;

/**
 * Listens for changes on an {@link ISENode}.
 * @author Martin Hentschel
 */
public interface ISEAnnotationLinkListener extends EventListener {
   /**
    * When a new {@link ISEAnnotationLink} was added via
    * {@link ISENode#addAnnotationLink(ISEAnnotationLink)}.
    * @param e The event.
    */
   public void annotationLinkAdded(SEAnnotationLinkEvent e);

   /**
    * When an existing {@link ISEAnnotationLink} was removed via
    * {@link ISENode#removeAnnotationLink(ISEAnnotationLink)}.
    * @param e The event.
    */
   public void annotationLinkRemoved(SEAnnotationLinkEvent e);
}
