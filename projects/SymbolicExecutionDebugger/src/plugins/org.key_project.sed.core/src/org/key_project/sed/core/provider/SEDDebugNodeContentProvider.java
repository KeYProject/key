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
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.internal.ui.model.elements.ElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IViewerUpdate;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.ISEDConstants;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * <p>
 * Implementation of {@link IElementContentProvider} that is used to
 * return the children of an {@link ISEDDebugNode} in normal or compact view. 
 * </p>
 * <p>
 * If {@link SEDPreferenceUtil#isShowCompactExecutionTree()} is {@code false}
 * the real containment hierarchy of {@link ISEDDebugNode}s is shown to the user.
 * In this case {@link #getChildren(Object)} returns just {@link ISEDDebugNode#getChildren()}.
 * </p>
 * <p>
 * If {@link SEDPreferenceUtil#isDefaultShowCompactExecutionTree()} is {@code true}
 * a compact symbolic execution tree is shown. It means that all following children
 * are returned as child of the given node until a child has not exactly one following child.
 * This hierarchy is computed via {@link #getCompactChildren(ISEDDebugNode)}. If
 * a node was reordered in this view can be checked via {@link #isCompactNode(ISEDDebugNode)}.
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDDebugNodeContentProvider extends ElementContentProvider {
   /**
    * The default instance.
    */
   private static SEDDebugNodeContentProvider defaultInsance;
   
   /**
    * Returns the default instance.
    * @return The default instance.
    */
   public static SEDDebugNodeContentProvider getDefaultInstance() {
      if (defaultInsance == null) {
         defaultInsance = new SEDDebugNodeContentProvider();
      }
      return defaultInsance;
   }
   
   /**
    * Returns the available children.
    * @param parent The parent element for that the children are needed.
    * @param context The {@link IPresentationContext} of the request.
    * @return The children. 
    * @throws CoreException Occurred Exception.
    */
   protected Object[] getAllChildren(Object parent, IPresentationContext context) throws CoreException {
      if (IDebugUIConstants.ID_VARIABLE_VIEW.equals(context.getId())) {
         if (parent instanceof IStackFrame) {
            IStackFrame frame = ((IStackFrame)parent);
            if (frame.hasVariables()) {
               return frame.getVariables();
            }
            else {
               return EMPTY;
            }
         }
         else {
            return EMPTY;
         }
      }
      else if (IDebugUIConstants.ID_REGISTER_VIEW.equals(context.getId())) {
         if (parent instanceof IStackFrame) {
            IStackFrame frame = ((IStackFrame)parent);
            if (frame.hasRegisterGroups()) {
               return frame.getRegisterGroups();
            }
            else {
               return EMPTY;
            }
         }
         else {
            return EMPTY;
         }
      }
      else if (ISEDConstants.ID_CALL_STACK.equals(context.getId())) {
         if (parent instanceof ISEDDebugNode) {
            Object root = context.getProperty(ISEDConstants.PRESENTATION_CONTEXT_PROPERTY_INPUT);
            if (root == null || root == parent) { // Return only children if it is the viewers input because otherwise the stack elements are expandable.
               ISEDDebugNode[] callStack = ((ISEDDebugNode)parent).getCallStack();
               return callStack != null ? callStack : EMPTY; 
            }
            else {
               return EMPTY;
            }
         }
         else {
            return EMPTY;
         }
      }
      else {
         return getAllDebugNodeChildren(parent);
      }
   }
   
   /**
    * Returns all children of the given parent in view "Debug".
    * @param parent The parent element.
    * @return The children.
    * @throws DebugException Occurred Exception
    */
   public Object[] getAllDebugNodeChildren(Object parent) throws DebugException {
      if (parent instanceof ISEDDebugNode) {
         if (SEDPreferenceUtil.isShowCompactExecutionTree()) {
            ISEDDebugNode node = (ISEDDebugNode)parent;
            if (!isCompactNode(node)) {
               Object[] children = getCompactChildren(node);
               return children != null ? children : EMPTY;
            }
            else {
               return EMPTY;
            }
         }
         else {
            Object[] children = ((ISEDDebugNode)parent).getChildren();
            return children != null ? children : EMPTY;
         }
      }
      else {
         return EMPTY;
      }
   }
   
   /**
    * Checks if the given {@link ISEDDebugNode} is a compact node in the
    * compact symbolic execution tree. Compact nodes have no children
    * in the view shown to the user.
    * @param node The {@link ISEDDebugNode} to check.
    * @return {@code true} is compact node and should have no children, {@code false} is no compact node and should have his children
    * @throws DebugException Occurred Exception.
    */
   protected boolean isCompactNode(ISEDDebugNode node) throws DebugException {
      if (node != null) {
         ISEDDebugNode parent = node.getParent();
         if (parent != null) {
            if (parent.getChildren().length >= 2) {
               return false;
            }
            else {
               Object[] children = getCompactChildren(node.getParent());
               return children.length >= 1 && children[children.length - 1] != node;
            }
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }

   /**
    * Returns the children in the compact symbolic execution tree view
    * of the given {@link ISEDDebugNode}. The idea is to return all following
    * real children in the containment hierarchy until a node is found
    * that has not exactly one child.
    * @param node The {@link ISEDDebugNode} for that the compact children are needed.
    * @return The compact children.
    * @throws DebugException Occurred Exception.
    */
   protected Object[] getCompactChildren(ISEDDebugNode node) throws DebugException {
      if (node != null) {
         ISEDDebugNode[] children = node.getChildren();
         if (children != null && children.length == 1) {
            ISEDDebugNode[] childChildren = children[0].getChildren();
            if (childChildren != null && childChildren.length == 1) {
               return ArrayUtil.addAll(children, getCompactChildren(children[0]));
            }
            else {
               return children;
            }
         }
         else {
            return children;
         }
      }
      else {
         return new Object[0];
      }
   }

   /**
    * Returns the parent of a given {@link ISEDDebugNode} as shown
    * in view "Debug".
    * @param element The current element.
    * @return Its parent shown in view "Debug".
    * @throws DebugException Occurred Exception
    */
   public Object getDebugNodeParent(Object element) throws DebugException {
      if (element instanceof ISEDThread) {
         return ((ISEDThread)element).getDebugTarget();
      }
      else if (element instanceof ISEDDebugNode) {
         ISEDDebugNode parent = ((ISEDDebugNode)element).getParent();
         if (SEDPreferenceUtil.isShowCompactExecutionTree()) {
            while (isCompactNode(parent)) {
               parent = parent.getParent();
            }
         }
         return parent;
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
      return getElements(getAllChildren(parent, context), index, length);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected int getChildCount(Object element, IPresentationContext context, IViewerUpdate monitor) throws CoreException {
      return getAllChildren(element, context).length;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean supportsContextId(String id) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(id) ||
             IDebugUIConstants.ID_VARIABLE_VIEW.equals(id) ||
             IDebugUIConstants.ID_REGISTER_VIEW.equals(id) ||
             ISEDConstants.ID_CALL_STACK.equals(id);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean hasChildren(Object element, IPresentationContext context, IViewerUpdate monitor) throws CoreException {
      if (IDebugUIConstants.ID_VARIABLE_VIEW.equals(context.getId())) {
         if (element instanceof IStackFrame) {
            return ((IStackFrame)element).hasVariables();
         }
         else {
            return false;
         }
      }
      else if (IDebugUIConstants.ID_REGISTER_VIEW.equals(context.getId())) {
         if (element instanceof IStackFrame) {
            return ((IStackFrame)element).hasRegisterGroups();
         }
         else {
            return false;
         }
      }
      else {
         return super.hasChildren(element, context, monitor);
      }
   }
}