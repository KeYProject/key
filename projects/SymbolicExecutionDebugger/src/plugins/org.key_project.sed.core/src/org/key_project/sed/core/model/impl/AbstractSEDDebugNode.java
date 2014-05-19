/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.core.model.impl;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IStep;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelSelectionPolicy;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelSelectionPolicyFactory;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.eclipse.debug.internal.ui.viewers.update.DefaultSelectionPolicy;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.event.ISEDAnnotationLinkListener;
import org.key_project.sed.core.model.event.SEDAnnotationLinkEvent;
import org.key_project.sed.core.provider.SEDDebugNodeContentProvider;
import org.key_project.sed.core.util.SEDAnnotationUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Provides a basic implementation of {@link ISEDDebugNode}.
 * </p>
 * <p>
 * Constructors should call {@link #initializeAnnotations()} to initialize
 * a nwe node with {@link ISEDAnnotation}s.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
@SuppressWarnings("restriction")
public abstract class AbstractSEDDebugNode extends AbstractSEDDebugElement implements ISEDDebugNode {
   /**
    * The parent in that this node is contained as child.
    */
   private final ISEDDebugNode parent;
   
   /**
    * The thread.
    */
   private final ISEDThread thread;
   
   /**
    * All contained {@link ISEDAnnotationLink}s.
    */
   private final Set<ISEDAnnotationLink> annotationLinks = new LinkedHashSet<ISEDAnnotationLink>();
   
   /**
    * All registered {@link ISEDAnnotationLinkListener}.
    */
   private final List<ISEDAnnotationLinkListener> annotationLinkListener = new LinkedList<ISEDAnnotationLinkListener>();
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this node is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    */
   public AbstractSEDDebugNode(ISEDDebugTarget target, 
                               ISEDDebugNode parent, 
                               ISEDThread thread) {
      super(target);
      this.parent = parent;
      this.thread = thread;
   }
   
   /**
    * This method should be called as last step of all constructors to
    * initialize the new created node with annotations.
    */
   protected void initializeAnnotations() throws DebugException {
      SEDAnnotationUtil.initializeAnnotations(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode getParent() throws DebugException {
      return parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDThread getThread() {
      return thread;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addAnnotationLink(ISEDAnnotationLink link) {
      if (link != null) {
         Assert.isTrue(getDebugTarget().isRegistered(link.getSource()), "Annotation is not registered in debug target.");
         if (annotationLinks.add(link)) {
            link.getSource().addLink(link);
            fireAnnotationLinkAdded(new SEDAnnotationLinkEvent(this, link));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeAnnotationLink(ISEDAnnotationLink link) {
      if (link != null) {
         if (annotationLinks.remove(link)) {
            link.getSource().removeLink(link);
            fireAnnotationLinkRemoved(new SEDAnnotationLinkEvent(this, link));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotationLink[] getAnnotationLinks() {
      return annotationLinks.toArray(new ISEDAnnotationLink[annotationLinks.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotationLink[] getAnnotationLinks(ISEDAnnotationType type) {
      List<ISEDAnnotationLink> result = new LinkedList<ISEDAnnotationLink>();
      for (ISEDAnnotationLink link : annotationLinks) {
         if (ObjectUtil.equals(type, link.getSource().getType())) {
            result.add(link);
         }
      }
      return result.toArray(new ISEDAnnotationLink[result.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean containsAnnotationLink(ISEDAnnotationLink link) {
      return link != null && annotationLinks.contains(link);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotation[] computeUsedAnnotations() {
      if (!annotationLinks.isEmpty()) {
         // Compute used annotations defining a background color
         Set<ISEDAnnotation> annotations = new HashSet<ISEDAnnotation>();
         for (ISEDAnnotationLink link : annotationLinks) {
            annotations.add(link.getSource());
         }
         // Sort annotations if necessary
         if (annotations.size() == 1) {
            return annotations.toArray(new ISEDAnnotation[annotations.size()]);
         }
         else {
            ISEDAnnotation[] result = new ISEDAnnotation[annotations.size()];
            ISEDAnnotation[] allAnnotations = getDebugTarget().getRegisteredAnnotations();
            int i = 0;
            int resultIndex = 0;
            while (i < allAnnotations.length && resultIndex < result.length) {
               if (annotations.contains(allAnnotations[i])) {
                  result[resultIndex] = allAnnotations[i];
                  resultIndex++;
               }
               i++;
            }
            return result;
         }
      }
      else {
         return new ISEDAnnotation[0];
      }
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Class adapter) {
      if (IElementContentProvider.class.equals(adapter)) {
         // Change used content provider to show SED specific children instead of the default one from the debug API.
         return SEDDebugNodeContentProvider.getDefaultInstance();
      }
      else if (IModelSelectionPolicyFactory.class.equals(adapter)) {
         // Custom IModelSelectionPolicy are required because otherwise ISEDDebugNodes which don't implement IStackFrame are not programmatically selectable in debug view.
         return new IModelSelectionPolicyFactory() {
            @Override
            public IModelSelectionPolicy createModelSelectionPolicyAdapter(Object element, IPresentationContext context) {
               return new DefaultSelectionPolicy((IDebugElement)element) {
                  @Override
                  protected boolean overrides(Object existing, Object candidate) {
                     if (existing instanceof ISEDDebugElement && candidate instanceof ISEDDebugElement) {
                        // Handle symbolic debug elements like IStackFrames in super implementation
                        ISEDDebugElement curr = (ISEDDebugElement)existing;
                        ISEDDebugElement next = (ISEDDebugElement)candidate;
                        return curr.getDebugTarget().equals(next.getDebugTarget()) || !isSticky(existing);
                     }
                     else {
                        return super.overrides(existing, candidate);
                     }
                  }

                  @Override
                  protected boolean isSticky(Object element) {
                     if (element instanceof ISEDDebugElement) {
                        // Handle symbolic debug elements like IStackFrames in super implementation
                        ISEDDebugElement node = (ISEDDebugElement)element;
                        ISEDDebugTarget target = node.getDebugTarget();
                        if (target.isSuspended()) {
                           return true;
                        }
                        else {
                           if (node instanceof IStep) {
                              return ((IStep)node).isStepping();
                           }
                           else {
                              return false;
                           }
                        }
                     }
                     else {
                        return super.isSticky(element);
                     }
                  }
               };
            }
         };
      }
      else {
         return Platform.getAdapterManager().getAdapter(this, adapter);
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
   public String toString() {
      try {
         return getNodeType() + ": " + getName();
      }
      catch (DebugException e) {
         return e.getMessage();
      }
   }
}