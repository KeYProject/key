package org.key_project.sed.core.annotation.event;

import java.util.EventListener;

import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;

/**
 * Listens for changes on an {@link ISEAnnotation}.
 * @author Martin Hentschel
 */
public interface ISEAnnotationLinkListener extends EventListener {
   /**
    * When a new {@link ISEAnnotationLink} was added via
    * {@link ISEAnnotation#addLink(org.key_project.sed.core.annotation.ISEAnnotationLink)}.
    * @param e The event.
    */
   public void annotationLinkAdded(SEAnnotationLinkEvent e);

   /**
    * When an existing {@link ISEAnnotationLink} was removed via
    * {@link ISEAnnotation#removeLink(ISEAnnotationLink)}.
    * @param e The event.
    */
   public void annotationLinkRemoved(SEAnnotationLinkEvent e);
}
