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
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.debug.internal.ui.model.elements.ElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IViewerUpdate;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.key_project.sed.core.model.ISEBaseMethodReturn;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEGroupable;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.util.ISEConstants;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * <p>
 * Implementation of {@link IElementContentProvider} that is used to
 * return the children of an {@link ISENode} in normal or compact view. 
 * </p>
 * <p>
 * If {@link SEDPreferenceUtil#isShowCompactExecutionTree()} is {@code false}
 * the real containment hierarchy of {@link ISENode}s is shown to the user.
 * In this case {@link #getChildren(Object)} returns just {@link ISENode#getChildren()}.
 * </p>
 * <p>
 * If {@link SEDPreferenceUtil#isDefaultShowCompactExecutionTree()} is {@code true}
 * a compact symbolic execution tree is shown. It means that all following children
 * are returned as child of the given node until a child has not exactly one following child.
 * This hierarchy is computed via {@link #getCompactChildren(ISENode)}. If
 * a node was reordered in this view can be checked via {@link #isCompactNode(ISENode)}.
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDebugNodeContentProvider extends ElementContentProvider {
   /**
    * The default instance.
    */
   private static SEDebugNodeContentProvider defaultInsance;
   
   /**
    * Returns the default instance.
    * @return The default instance.
    */
   public static SEDebugNodeContentProvider getDefaultInstance() {
      if (defaultInsance == null) {
         defaultInsance = new SEDebugNodeContentProvider();
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
      else if (ISEConstants.ID_CALL_STACK.equals(context.getId())) {
         if (parent instanceof ISENode) {
            Object root = context.getProperty(ISEConstants.PRESENTATION_CONTEXT_PROPERTY_INPUT);
            if (root == null || root == parent) { // Return only children if it is the viewers input because otherwise the stack elements are expandable.
               ISENode[] callStack = ((ISENode)parent).getCallStack();
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
      else if (ISEConstants.ID_CALL_STATE.equals(context.getId())) {
         if (parent instanceof ISEBaseMethodReturn) {
            IVariable[] callState = ((ISEBaseMethodReturn)parent).getCallStateVariables();
            return callState != null ? callState : EMPTY; 
         }
         else {
            return EMPTY;
         }
      }
      else if (ISEConstants.ID_METHOD_RETURN_CONDITIONS.equals(context.getId())) {
         if (parent instanceof ISEMethodCall) {
            Object root = context.getProperty(ISEConstants.PRESENTATION_CONTEXT_PROPERTY_INPUT);
            if (root == null || root == parent) { // Return only children if it is the viewers input because otherwise the stack elements are expandable.
               ISEBranchCondition[] conditions = ((ISEMethodCall)parent).getMethodReturnConditions();
               return conditions != null ? conditions : EMPTY; 
            }
            else {
               return EMPTY;
            }
         }
         if (parent instanceof ISEBranchCondition) {
            ISENode[] children = ((ISENode)parent).getChildren();
            return children != null ? children : EMPTY; 
         }
         else {
            return EMPTY;
         }
      }
      else if (ISEConstants.ID_GROUP_END_CONDITIONS.equals(context.getId())) {
         Object root = context.getProperty(ISEConstants.PRESENTATION_CONTEXT_PROPERTY_INPUT);
         if (parent == root) {
            ISEBranchCondition[] conditions = ((ISEGroupable)parent).getGroupEndConditions();
            return conditions != null ? conditions : EMPTY; 
         }
         else if (parent instanceof ISEBranchCondition) {
            ISEBranchCondition[] conditions = ((ISEGroupable)root).getGroupEndConditions();
            if (ArrayUtil.contains(conditions, parent)) { // Otherwise branch condition children as child of end condition would be shown.
               ISENode[] children = ((ISENode)parent).getChildren();
               return children != null ? children : EMPTY; 
            }
            else {
               return EMPTY;
            }
         }
         else {
            return EMPTY;
         }
      }
      else if (ISEConstants.ID_GROUP_START_CONDITIONS.equals(context.getId())) {
         Object root = context.getProperty(ISEConstants.PRESENTATION_CONTEXT_PROPERTY_INPUT);
         if (parent == root) {
            ISEBranchCondition[] conditions = ((ISENode)parent).getGroupStartConditions();
            return conditions != null ? conditions : EMPTY; 
         }
         else if (parent instanceof ISEBranchCondition) {
            ISENode parentParent = ((ISENode)parent).getParent();
            return parentParent != null ? new Object[] {parentParent} : EMPTY; 
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
      if (parent instanceof ISENode) {
         if (SEDPreferenceUtil.isShowCompactExecutionTree()) {
            ISENode node = (ISENode)parent;
            if (!isCompactNode(node)) {
               Object[] children = getCompactChildren(node);
               return children != null ? children : EMPTY;
            }
            else {
               return EMPTY;
            }
         }
         else {
            if (parent instanceof ISEGroupable &&
                ((ISEGroupable) parent).isCollapsed()) {
               ISEBranchCondition[] endConditions = ((ISEGroupable) parent).getGroupEndConditions();
               return endConditions != null ? endConditions : EMPTY;
            }
            else {
               Object[] children = ((ISENode)parent).getChildren();
               return children != null ? children : EMPTY;
            }
         }
      }
      else {
         return EMPTY;
      }
   }
   
   /**
    * Checks if the given {@link ISENode} is a compact node in the
    * compact symbolic execution tree. Compact nodes have no children
    * in the view shown to the user.
    * @param node The {@link ISENode} to check.
    * @return {@code true} is compact node and should have no children, {@code false} is no compact node and should have his children
    * @throws DebugException Occurred Exception.
    */
   protected boolean isCompactNode(ISENode node) throws DebugException {
      if (node != null) {
         ISENode parent = node.getParent();
         if (parent != null) {
            if (parent instanceof ISEGroupable &&
                ((ISEGroupable) parent).isCollapsed() &&
                ((ISEGroupable) parent).getGroupEndConditions().length >= 2) {
               return false;
            }
            else if (parent.getChildren().length >= 2) {
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
    * of the given {@link ISENode}. The idea is to return all following
    * real children in the containment hierarchy until a node is found
    * that has not exactly one child.
    * @param node The {@link ISENode} for that the compact children are needed.
    * @return The compact children.
    * @throws DebugException Occurred Exception.
    */
   protected Object[] getCompactChildren(ISENode node) throws DebugException {
      if (node != null) {
         ISENode[] children = node instanceof ISEGroupable && ((ISEGroupable) node).isCollapsed() ?
                                    ((ISEGroupable) node).getGroupEndConditions() :
                                    node.getChildren();
         if (children != null && children.length == 1) {
            ISENode[] childChildren = children[0] instanceof ISEGroupable && ((ISEGroupable) children[0]).isCollapsed() ?
                                            ((ISEGroupable) children[0]).getGroupEndConditions() :
                                            children[0].getChildren();
            if (childChildren != null && childChildren.length == 1) {
               return ArrayUtil.addAll(children, getCompactChildren(children[0]), ISENode.class);
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
    * Returns the parent of a given {@link ISENode} as shown
    * in view "Debug".
    * @param element The current element.
    * @return Its parent shown in view "Debug".
    * @throws DebugException Occurred Exception
    */
   public Object getDebugNodeParent(Object element) throws DebugException {
      if (element instanceof ISEThread) {
         return ((ISEThread)element).getDebugTarget();
      }
      else if (element instanceof ISENode) {
         ISENode parent = getShownParent((ISENode) element);
         if (SEDPreferenceUtil.isShowCompactExecutionTree()) {
            while (isCompactNode(parent)) {
               parent = getShownParent(parent);
            }
         }
         return parent;
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the shown parent of the given {@link ISENode} which
    * is {@link ISENode#getParent()} in case that the start node is not
    * collapsed or the outer most visible parent.
    * @param node The {@link ISENode} to compute its parent.
    * @return The computed parent or {@code null} if the node has no parent.
    * @throws DebugException Occurred Exception.
    */
   protected ISENode getShownParent(ISENode node) throws DebugException {
      ISEBranchCondition[] startConditions = node.getGroupStartConditions();
      ISENode parent = null;
      if (startConditions != null) {
         int i = 0;
         while (parent == null && i < startConditions.length) {
            ISENode startNode = startConditions[i].getParent();
            if (startNode instanceof ISEGroupable &&
                ((ISEGroupable) startNode).isCollapsed()) {
               parent = startConditions[i];
            }
            i++;
         }
      }
      return parent != null ? parent : node.getParent();
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
             ISEConstants.ID_CALL_STACK.equals(id) ||
             ISEConstants.ID_CALL_STATE.equals(id) ||
             ISEConstants.ID_METHOD_RETURN_CONDITIONS.equals(id) ||
             ISEConstants.ID_GROUP_START_CONDITIONS.equals(id) ||
             ISEConstants.ID_GROUP_END_CONDITIONS.equals(id);
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

   /**
    * Checks if the given {@link ISENode} is shown.
    * @param element The {@link ISENode} to check.
    * @return {@code true} is shown, {@code false} is not shown.
    * @throws DebugException Occurred Exception.
    */
   public boolean isShown(ISENode element) throws DebugException {
      if (element != null) {
         boolean shown = true;
         while (element != null && shown) {
            ISENode parent = element.getParent();
            if (parent instanceof ISEGroupable) {
               ISEGroupable groupable = (ISEGroupable) parent;
               if (groupable.isCollapsed()) {
                  if (parent instanceof ISENode &&
                      ArrayUtil.contains(((ISENode) parent).getChildren(), element)) {
                     shown = false;
                  }                  
               }
               else {
                  if (ArrayUtil.contains(((ISEGroupable) parent).getGroupEndConditions(), element)) {
                     shown = false;
                  }
               }
            }
            element = parent;
         }
         return shown;
      }
      else {
         return false;
      }
   }
}