/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IStep;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelSelectionPolicy;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelSelectionPolicyFactory;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.eclipse.debug.internal.ui.viewers.update.DefaultSelectionPolicy;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.provider.SEDDebugNodeContentProvider;

/**
 * Provides a basic implementation of {@link ISEDDebugNode}.
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
@SuppressWarnings("restriction")
public abstract class AbstractSEDDebugNode extends AbstractSEDDebugElement implements ISEDDebugNode {
   /**
    * The parent in that this node is contained as child.
    */
   private ISEDDebugNode parent;
   
   /**
    * The thread.
    */
   private ISEDThread thread;
   
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
   public String toString() {
      try {
         return getNodeType() + ": " + getName();
      }
      catch (DebugException e) {
         return e.getMessage();
      }
   }
}