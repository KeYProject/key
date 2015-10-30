package org.key_project.sed.core.annotation.impl;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.annotation.event.ISEAnnotationLinkListener;
import org.key_project.sed.core.annotation.event.SEAnnotationLinkEvent;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.impl.AbstractSEDebugElement;

/**
 * Provides the basic functionality of {@link ISEAnnotation}s.
 * @author Martin Hentschel
 */
public abstract class AbstractSEAnnotation extends AbstractSEAnnotationAppearance implements ISEAnnotation {
   /**
    * The unique ID.
    */
   private String id;
   
   /**
    * The enabled state.
    */
   private boolean enabled;
   
   /**
    * All contained {@link ISEAnnotationLink}s.
    */
   private final List<ISEAnnotationLink> links = new LinkedList<ISEAnnotationLink>();
   
   /**
    * All registered {@link ISEAnnotationLinkListener}.
    */
   private final List<ISEAnnotationLinkListener> annotationLinkListener = new LinkedList<ISEAnnotationLinkListener>();
   
   /**
    * Constructor.
    * @param type The type of this annotation.
    * @param enabled The initial enabled state.
    */
   public AbstractSEAnnotation(ISEAnnotationType type, boolean enabled) {
      super(type);
      this.enabled = enabled;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addLink(ISEAnnotationLink link) {
      if (link != null) {
         Assert.isTrue(link.getTarget().getDebugTarget().isRegistered(this), "Annotation is not registered in debug target.");
         if (!links.contains(link)) {
            links.add(link);
            link.getTarget().addAnnotationLink(link);
            fireAnnotationLinkAdded(new SEAnnotationLinkEvent(this, link));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeLink(ISEAnnotationLink link) {
      if (link != null) {
         if (links.remove(link)) {
            link.getTarget().removeAnnotationLink(link);
            fireAnnotationLinkRemoved(new SEAnnotationLinkEvent(this, link));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotationLink[] getLinks() {
      return links.toArray(new ISEAnnotationLink[links.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotationLink getLinkAt(int index) {
      if (index >= 0 && index < links.size()) {
         return links.get(index);
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean containsLink(ISEAnnotationLink link) {
      return link != null && links.contains(link);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int countLinks() {
      return links.size();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasLinks() {
      return !links.isEmpty();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int indexOfLink(ISEAnnotationLink link) {
      return link != null ? links.indexOf(link) : -1;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Set<ISENode> listLinkTargets() {
      Set<ISENode> targets = new LinkedHashSet<ISENode>();
      for (ISEAnnotationLink link : links) {
         targets.add(link.getTarget());
      }
      return targets;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isEnabled() {
      return enabled;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setEnabled(boolean enabled) {
      boolean oldValue = isEnabled();
      this.enabled = enabled;
      firePropertyChange(PROP_ENABLED, oldValue, isEnabled());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void delete(ISEDebugTarget target) {
      if (target != null) {
         target.unregisterAnnotation(this);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addAnnotationLinkListener(ISEAnnotationLinkListener l) {
      if (l != null) {
         annotationLinkListener.add(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeAnnotationLinkListener(ISEAnnotationLinkListener l) {
      if (l != null) {
         annotationLinkListener.remove(l);
      }
   }
   
   /**
    * Fires the event {@link ISEAnnotationLinkListener#annotationLinkAdded(SEAnnotationLinkEvent)}.
    * @param e The {@link SEAnnotationLinkEvent}.
    */
   protected void fireAnnotationLinkAdded(SEAnnotationLinkEvent e) {
      ISEAnnotationLinkListener[] listener = annotationLinkListener.toArray(new ISEAnnotationLinkListener[annotationLinkListener.size()]);
      for (ISEAnnotationLinkListener l : listener) {
         l.annotationLinkAdded(e);
      }
   }
   
   /**
    * Fires the event {@link ISEAnnotationLinkListener#annotationLinkRemoved(SEAnnotationLinkEvent)}.
    * @param e The {@link SEAnnotationLinkEvent}.
    */
   protected void fireAnnotationLinkRemoved(SEAnnotationLinkEvent e) {
      ISEAnnotationLinkListener[] listener = annotationLinkListener.toArray(new ISEAnnotationLinkListener[annotationLinkListener.size()]);
      for (ISEAnnotationLinkListener l : listener) {
         l.annotationLinkRemoved(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      if (id == null) {
         synchronized (this) {
            if (id == null) {
               id = AbstractSEDebugElement.computeNewId();
            }
         }
      }
      return id;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setId(String id) {
      Assert.isTrue(this.id == null, "Can't change an already existing ID.");
      this.id = id;
   }
}
