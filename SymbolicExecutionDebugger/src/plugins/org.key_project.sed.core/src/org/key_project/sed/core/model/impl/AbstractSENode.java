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
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IStep;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelSelectionPolicy;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelSelectionPolicyFactory;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.eclipse.debug.internal.ui.viewers.update.DefaultSelectionPolicy;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEGroupable;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.event.ISEAnnotationLinkListener;
import org.key_project.sed.core.model.event.SEAnnotationLinkEvent;
import org.key_project.sed.core.provider.SEDebugNodeContentProvider;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Provides a basic implementation of {@link ISENode}.
 * </p>
 * <p>
 * Constructors should call {@link #initializeAnnotations()} to initialize
 * a nwe node with {@link ISEAnnotation}s.
 * </p>
 * @author Martin Hentschel
 * @see ISENode
 */
@SuppressWarnings("restriction")
public abstract class AbstractSENode extends AbstractSEDebugElement implements ISENode {
   /**
    * The parent in that this node is contained as child.
    */
   private ISENode parent;
   
   /**
    * The thread.
    */
   private final ISEThread thread;
   
   /**
    * All contained {@link ISEAnnotationLink}s.
    */
   private final Set<ISEAnnotationLink> annotationLinks = new LinkedHashSet<ISEAnnotationLink>();
   
   /**
    * All registered {@link ISEAnnotationLinkListener}.
    */
   private final List<ISEAnnotationLinkListener> annotationLinkListener = new LinkedList<ISEAnnotationLinkListener>();
   
   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this node is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEThread} in that this node is contained.
    */
   public AbstractSENode(ISEDebugTarget target, 
                               ISENode parent, 
                               ISEThread thread) {
      super(target);
      this.parent = parent;
      this.thread = thread;
   }
   
   /**
    * This method should be called as last step of all constructors to
    * initialize the new created node with annotations.
    */
   protected void initializeAnnotations() throws DebugException {
      SEAnnotationUtil.initializeAnnotations(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISENode getParent() throws DebugException {
      return parent;
   }
   
   /**
    * It is valid to set the parent as long it was not defined before.
    * So a parent might be set lazily later but can never be changed.
    * @param parent The new parent to set.
    */
   protected void setParent(ISENode parent) {
      Assert.isTrue(this.parent == null || this.parent == parent);
      this.parent = parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEThread getThread() {
      return thread;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addAnnotationLink(ISEAnnotationLink link) {
      if (link != null) {
         Assert.isTrue(getDebugTarget().isRegistered(link.getSource()), "Annotation is not registered in debug target.");
         if (annotationLinks.add(link)) {
            link.getSource().addLink(link);
            fireAnnotationLinkAdded(new SEAnnotationLinkEvent(this, link));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeAnnotationLink(ISEAnnotationLink link) {
      if (link != null) {
         if (annotationLinks.remove(link)) {
            link.getSource().removeLink(link);
            fireAnnotationLinkRemoved(new SEAnnotationLinkEvent(this, link));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotationLink[] getAnnotationLinks() {
      return annotationLinks.toArray(new ISEAnnotationLink[annotationLinks.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotationLink[] getAnnotationLinks(ISEAnnotationType type) {
      List<ISEAnnotationLink> result = new LinkedList<ISEAnnotationLink>();
      for (ISEAnnotationLink link : annotationLinks) {
         if (ObjectUtil.equals(type, link.getSource().getType())) {
            result.add(link);
         }
      }
      return result.toArray(new ISEAnnotationLink[result.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean containsAnnotationLink(ISEAnnotationLink link) {
      return link != null && annotationLinks.contains(link);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotation[] computeUsedAnnotations() {
      if (!annotationLinks.isEmpty()) {
         // Compute used annotations defining a background color
         Set<ISEAnnotation> annotations = new HashSet<ISEAnnotation>();
         for (ISEAnnotationLink link : annotationLinks) {
            annotations.add(link.getSource());
         }
         // Sort annotations if necessary
         if (annotations.size() == 1) {
            return annotations.toArray(new ISEAnnotation[annotations.size()]);
         }
         else {
            ISEAnnotation[] result = new ISEAnnotation[annotations.size()];
            ISEAnnotation[] allAnnotations = getDebugTarget().getRegisteredAnnotations();
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
         return new ISEAnnotation[0];
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
         return SEDebugNodeContentProvider.getDefaultInstance();
      }
      else if (IModelSelectionPolicyFactory.class.equals(adapter)) {
         // Custom IModelSelectionPolicy are required because otherwise ISEDDebugNodes which don't implement IStackFrame are not programmatically selectable in debug view.
         return new IModelSelectionPolicyFactory() {
            @Override
            public IModelSelectionPolicy createModelSelectionPolicyAdapter(Object element, IPresentationContext context) {
               return new DefaultSelectionPolicy((IDebugElement)element) {
                  @Override
                  protected boolean overrides(Object existing, Object candidate) {
                     if (existing instanceof ISEDebugElement && candidate instanceof ISEDebugElement) {
                        // Handle symbolic debug elements like IStackFrames in super implementation
                        ISEDebugElement curr = (ISEDebugElement)existing;
                        ISEDebugElement next = (ISEDebugElement)candidate;
                        return curr.getDebugTarget().equals(next.getDebugTarget()) || !isSticky(existing);
                     }
                     else {
                        return super.overrides(existing, candidate);
                     }
                  }

                  @Override
                  protected boolean isSticky(Object element) {
                     if (element instanceof ISEDebugElement) {
                        // Handle symbolic debug elements like IStackFrames in super implementation
                        ISEDebugElement node = (ISEDebugElement)element;
                        ISEDebugTarget target = node.getDebugTarget();
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
   public boolean hasChildren() throws DebugException {
      ISENode[] children = getChildren();
      return !ArrayUtil.isEmpty(children);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasConstraints() throws DebugException {
      ISEConstraint[] constraints = getConstraints();
      return !ArrayUtil.isEmpty(constraints);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IBreakpoint[] computeHitBreakpoints() throws DebugException {
      return getDebugTarget().computeHitBreakpoints(this);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ISEBranchCondition getGroupStartCondition(final ISENode startNode) throws DebugException {
      ISEBranchCondition[] conditions = getGroupStartConditions();
      return ArrayUtil.search(conditions, new IFilter<ISEBranchCondition>() {
         @Override
         public boolean select(ISEBranchCondition element) {
            try {
               return element.getParent() == startNode;
            }
            catch (DebugException e) {
               return false;
            }
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEBranchCondition getInnerMostVisibleGroupStartCondition() throws DebugException {
      ISEBranchCondition result = null;
      ISEBranchCondition[] startConditions = getGroupStartConditions();
      if (startConditions != null) {
         // Find first collapsed condition.
         int i = 0;
         while (result == null && i < startConditions.length) {
            ISENode parent = startConditions[i].getParent();
            if (parent instanceof ISEGroupable) {
               if (((ISEGroupable) parent).isCollapsed()) {
                  result = startConditions[i];
               }
            }
            i++;
         }
         // Return last branch condition if none of them is collapsed.
         if (result == null && startConditions.length >= 1) {
            result = startConditions[startConditions.length - 1];
         }
      }
      return result;
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