package org.key_project.sed.core.annotation.event;

import java.util.EventListener;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;

/**
 * Listens for changes on an {@link ISEDAnnotation}.
 * @author Martin Hentschel
 */
public interface ISEDAnnotationLinkListener extends EventListener {
   /**
    * When a new {@link ISEDAnnotationLink} was added via
    * {@link ISEDAnnotation#addLink(org.key_project.sed.core.annotation.ISEDAnnotationLink)}.
    * @param e The event.
    */
   public void annotationLinkAdded(SEDAnnotationLinkEvent e);

   /**
    * When an existing {@link ISEDAnnotationLink} was removed via
    * {@link ISEDAnnotation#removeLink(ISEDAnnotationLink)}.
    * @param e The event.
    */
   public void annotationLinkRemoved(SEDAnnotationLinkEvent e);
}
