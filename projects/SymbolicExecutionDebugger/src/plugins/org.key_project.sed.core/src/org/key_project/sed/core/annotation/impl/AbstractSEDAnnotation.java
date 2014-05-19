package org.key_project.sed.core.annotation.impl;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.annotation.event.ISEDAnnotationLinkListener;
import org.key_project.sed.core.annotation.event.SEDAnnotationLinkEvent;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.impl.AbstractSEDDebugElement;
import org.key_project.util.bean.Bean;

/**
 * Provides the basic functionality of {@link ISEDAnnotation}s.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDAnnotation extends Bean implements ISEDAnnotation {
   /**
    * The unique ID.
    */
   private String id;
   
   /**
    * The enabled state.
    */
   private boolean enabled;

   /**
    * The type of this annotation.
    */
   private final ISEDAnnotationType type;
   
   /**
    * All contained {@link ISEDAnnotationLink}s.
    */
   private final List<ISEDAnnotationLink> links = new LinkedList<ISEDAnnotationLink>();

   /**
    * The custom background highlighting.
    */
   private Boolean customHighlightBackground;

   /**
    * The custom background color.
    */
   private RGB customBackgroundColor;
   
   /**
    * The custom foreground highlighting.
    */
   private Boolean customHighlightForeground;

   /**
    * The custom foreground color.
    */
   private RGB customForegroundColor;
   
   /**
    * All registered {@link ISEDAnnotationLinkListener}.
    */
   private final List<ISEDAnnotationLinkListener> annotationLinkListener = new LinkedList<ISEDAnnotationLinkListener>();
   
   /**
    * Constructor.
    * @param type The type of this annotation.
    * @param enabled The initial enabled state.
    */
   public AbstractSEDAnnotation(ISEDAnnotationType type, boolean enabled) {
      Assert.isNotNull(type);
      this.type = type;
      this.enabled = enabled;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addLink(ISEDAnnotationLink link) {
      if (link != null) {
         Assert.isTrue(link.getTarget().getDebugTarget().isRegistered(this), "Annotation is not registered in debug target.");
         if (!links.contains(link)) {
            links.add(link);
            link.getTarget().addAnnotationLink(link);
            fireAnnotationLinkAdded(new SEDAnnotationLinkEvent(this, link));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeLink(ISEDAnnotationLink link) {
      if (link != null) {
         if (links.remove(link)) {
            link.getTarget().removeAnnotationLink(link);
            fireAnnotationLinkRemoved(new SEDAnnotationLinkEvent(this, link));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotationLink[] getLinks() {
      return links.toArray(new ISEDAnnotationLink[links.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotationLink getLinkAt(int index) {
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
   public boolean containsLink(ISEDAnnotationLink link) {
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
   public int indexOfLink(ISEDAnnotationLink link) {
      return link != null ? links.indexOf(link) : -1;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Set<ISEDDebugNode> listLinkTargets() {
      Set<ISEDDebugNode> targets = new LinkedHashSet<ISEDDebugNode>();
      for (ISEDAnnotationLink link : links) {
         targets.add(link.getTarget());
      }
      return targets;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotationType getType() {
      return type;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isHighlightBackground() {
      if (customHighlightBackground != null) {
         return customHighlightBackground.booleanValue();
      }
      else {
         return type.isHighlightBackground();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getBackgroundColor() {
      if (customBackgroundColor != null) {
         return customBackgroundColor;
      }
      else {
         return type.getBackgroundColor();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isHighlightForeground() {
      if (customHighlightForeground != null) {
         return customHighlightForeground.booleanValue();
      }
      else {
         return type.isHighlightForeground();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getForegroundColor() {
      if (customForegroundColor != null) {
         return customForegroundColor;
      }
      else {
         return type.getForegroundColor();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setCustomHighlightBackground(Boolean customHighlightBackground) {
      boolean oldValue = isHighlightBackground();
      this.customHighlightBackground = customHighlightBackground;
      firePropertyChange(PROP_HIGHLIGHT_BACKGROUND, oldValue, isHighlightBackground());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setCustomBackgroundColor(RGB customBackgroundColor) {
      RGB oldValue = getBackgroundColor();
      this.customBackgroundColor = customBackgroundColor;
      firePropertyChange(PROP_BACKGROUND_COLOR, oldValue, getBackgroundColor());
   }

   /**
    * {@inheritDoc}
    */
   @Override   
   public void setCustomHighlightForeground(Boolean customHighlightForeground) {
      boolean oldValue = isHighlightForeground();
      this.customHighlightForeground = customHighlightForeground;
      firePropertyChange(PROP_HIGHLIGHT_FOREGROUND, oldValue, isHighlightForeground());
   }

   /**
    * {@inheritDoc}
    */
   @Override   
   public void setCustomForegroundColor(RGB customForegroundColor) {
      RGB oldValue = getForegroundColor();
      this.customForegroundColor = customForegroundColor;
      firePropertyChange(PROP_FOREGROUND_COLOR, oldValue, getForegroundColor());
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
   public void delete(ISEDDebugTarget target) {
      if (target != null) {
         target.unregisterAnnotation(this);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addAnnotationLinkListener(ISEDAnnotationLinkListener l) {
      if (l != null) {
         annotationLinkListener.add(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeAnnotationLinkListener(ISEDAnnotationLinkListener l) {
      if (l != null) {
         annotationLinkListener.remove(l);
      }
   }
   
   /**
    * Fires the event {@link ISEDAnnotationLinkListener#annotationLinkAdded(SEDAnnotationLinkEvent)}.
    * @param e The {@link SEDAnnotationLinkEvent}.
    */
   protected void fireAnnotationLinkAdded(SEDAnnotationLinkEvent e) {
      ISEDAnnotationLinkListener[] listener = annotationLinkListener.toArray(new ISEDAnnotationLinkListener[annotationLinkListener.size()]);
      for (ISEDAnnotationLinkListener l : listener) {
         l.annotationLinkAdded(e);
      }
   }
   
   /**
    * Fires the event {@link ISEDAnnotationLinkListener#annotationLinkRemoved(SEDAnnotationLinkEvent)}.
    * @param e The {@link SEDAnnotationLinkEvent}.
    */
   protected void fireAnnotationLinkRemoved(SEDAnnotationLinkEvent e) {
      ISEDAnnotationLinkListener[] listener = annotationLinkListener.toArray(new ISEDAnnotationLinkListener[annotationLinkListener.size()]);
      for (ISEDAnnotationLinkListener l : listener) {
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
               id = AbstractSEDDebugElement.computeNewId();
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
