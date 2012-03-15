package org.key_project.sed.core.provider;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.internal.ui.model.elements.ElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IViewerUpdate;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.key_project.sed.core.model.ISEDDebugNode;
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
 * a node was reordered in this view can be checked via {@link #isCompactNod(ISEDDebugNode)}.
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
    * @return The children. 
    * @throws CoreException Occurred Exception.
    */
   protected Object[] getChildren(Object parent) throws CoreException {
      if (parent instanceof ISEDDebugNode) {
         if (SEDPreferenceUtil.isShowCompactExecutionTree()) {
            ISEDDebugNode node = (ISEDDebugNode)parent;
            if (!isCompactNod(node)) {
               Object[] children = getCompactChildren(node);
               return children != null ? children : new Object[0];
            }
            else {
               return new Object[0];
            }
         }
         else {
            Object[] children = ((ISEDDebugNode)parent).getChildren();
            return children != null ? children : new Object[0];
         }
      }
      else {
         return new Object[0];
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
   protected boolean isCompactNod(ISEDDebugNode node) throws DebugException {
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
    * {@inheritDoc}
    */
   @Override
   protected Object[] getChildren(Object parent, int index, int length, IPresentationContext context, IViewerUpdate monitor) throws CoreException {
      return getElements(getChildren(parent), index, length);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected int getChildCount(Object element, IPresentationContext context, IViewerUpdate monitor) throws CoreException {
      return getChildren(element).length;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean supportsContextId(String id) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(id);
   }
}
