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

package org.key_project.sed.core.provider;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IThread;
import org.eclipse.debug.internal.ui.model.elements.ElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IViewerUpdate;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.impl.AbstractSEDebugTarget;

/**
 * <p>
 * Implementation of {@link IElementContentProvider} that is used in the
 * debug API to return the symbolic threads ({@link ISEThread}) instead
 * of the normal threads ({@link IThread}) of a given {@link ISEDebugTarget}.
 * </p>
 * <p>
 * To make sure that this implementation is used instead of the default
 * one on {@link IDebugTarget}s, it is required to return an instance
 * directly in {@link IDebugTarget#getAdapter(Class)} as implemented in
 * {@link AbstractSEDebugTarget}.
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDebugTargetContentProvider extends ElementContentProvider {
   /**
    * The default instance.
    */
   private static SEDebugTargetContentProvider defaultInsance;
   
   /**
    * Returns the default instance.
    * @return The default instance.
    */
   public static SEDebugTargetContentProvider getDefaultInstance() {
      if (defaultInsance == null) {
         defaultInsance = new SEDebugTargetContentProvider();
      }
      return defaultInsance;
   }
   
   /**
    * Returns the available children.
    * @param parent The parent element for that the children are needed.
    * @return The children. 
    * @throws DebugException Occurred Exception.
    */
   public Object[] getAllChildren(Object parent) throws DebugException {
      if (parent instanceof ISEDebugTarget) {
         Object[] children = ((ISEDebugTarget)parent).getSymbolicThreads();
         return children != null ? children : EMPTY;
      }
      else {
         return EMPTY;
      }
   }
   
   /**
    * Returns the parent element of the given one.
    * @param element The given element.
    * @return The parent element.
    * @throws DebugException Occurred Exception.
    */
   public Object getParent(Object element) throws DebugException {
      if (element instanceof ISEDebugTarget) {
         return ((ISEDebugTarget)element).getLaunch();
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Object[] getChildren(Object parent, int index, int length, IPresentationContext context, IViewerUpdate monitor) throws CoreException {
      return getElements(getAllChildren(parent), index, length);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected int getChildCount(Object element, IPresentationContext context, IViewerUpdate monitor) throws CoreException {
      return getAllChildren(element).length;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean supportsContextId(String id) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(id);
   }
}