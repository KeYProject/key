package org.key_project.sed.core.util;

import java.util.LinkedList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEGroupable;
import org.key_project.util.java.ArrayUtil;

/**
 * Provides static methods for {@link ISENode} for
 * navigating in the tree.
 * @author Martin Möller
 */
public final class NodeUtil {
   
   /**
    * Forbid instances.
    */
   private NodeUtil() {
   }
   
   /**
    * Returns the parent node of the given {@link ISENode}.
    * If the given {@link ISENode} end a collapsed group it will
    * return the specific {@link ISEBranchCondition}.
    * @param node The {@link ISENode} to get the parent for.
    * @return The parent {@link ISENode} of the given node.
    * @throws DebugException Occurred Exception.
    */
   public static ISENode getParent(ISENode node) throws DebugException {
      if(!ArrayUtil.isEmpty(node.getGroupStartConditions())) {
         ISEBranchCondition bc = node.getInnerMostVisibleGroupStartCondition();

         if(canBeGrouped(bc.getParent()) && ((ISEGroupable)bc.getParent()).isCollapsed()) {
            return bc;
         }  
      }

      return node.getParent();
   }
   
   /**
    * Returns all children of the given {@link ISENode}. If
    * {@link NodeUtil#canBeGrouped(Object)} and {@link ISEGroupable#isCollapsed()}
    * are true it will return all {@link ISEDBranchConditions} to the end nodes sorted
    * from left to right.
    * @param node The {@link ISENode} to get the children for.
    * @return The sorted children as {@link ISEBranchCondition}-Array. 
    * @throws DebugException Occured Exception.
    */
   public static ISENode[] getChildren(ISENode node) throws DebugException {
      if(canBeGrouped(node)) {
         ISEGroupable groupStart = (ISEGroupable) node;
         if(groupStart.isCollapsed()) {
            return getSortedBCs(groupStart);
         }
      }

      return node.getChildren();
   }
   
   /**
    * Returns the sorted {@link ISEBranchCondition}s of the given {@link ISEGroupable}.
    * @param groupStart The {@link ISEGroupable} to get the {@link ISEBranchCondition}s for.
    * @return The sorted {@link ISEBranchCondition}s.
    * @throws DebugException Occured Exception.
    */
   public static ISEBranchCondition[] getSortedBCs(ISEGroupable groupStart) throws DebugException {
      LinkedList<ISENode> orderedBCs = new LinkedList<ISENode>();
      
      ISENode next = determineNextNode((ISENode) groupStart, (ISENode) groupStart, false);
      while (next != null)
      {
         boolean groupEndReached = false;
         
         ISENode bc = next.getGroupStartCondition((ISENode) groupStart);
         
         if(bc != null) {
            orderedBCs.add(bc);
            groupEndReached = true;
         }
         
         next = determineNextNode(next, (ISENode) groupStart, groupEndReached);
      }
   
      return orderedBCs.toArray(new ISEBranchCondition[orderedBCs.size()]);
   }
   
   /**
    * Returns the startnode of the group in which the given {@link ISENode} lies.   
    * @param node The {@link ISENode} to get the group startnode for.
    * @return The {@link ISEGroupable} of the group of the given {@link ISENode}.
    * @throws DebugException Occured Exception.
    */
   public static ISEGroupable getGroupStartNode(ISENode node) throws DebugException {
      
      if(node == null) {
         return null;
      }

      if(!ArrayUtil.isEmpty(node.getGroupStartConditions())) {
         return (ISEGroupable) getParent(node.getInnerMostVisibleGroupStartCondition());
      }
      
      int currentPosition = -1;
      
      ISENode parent = getParent(node);
      while(parent != null) {
         if(canBeGrouped(parent)) {
            currentPosition++;
         }
         else if(!ArrayUtil.isEmpty(parent.getGroupStartConditions())) {
            int index = ArrayUtil.indexOf(parent.getGroupStartConditions(), parent.getInnerMostVisibleGroupStartCondition());
            currentPosition -= index + 1;
         }

         if(currentPosition == 0) {
            return (ISEGroupable) parent;
         }
         
         parent = getParent(parent);
      }

      return null;
   }
   
   /**
    * Determines if the given {@link Object} is an instance of {@link ISEGroupable} and
    * {@link ISEGroupable#isGroupable()}.
    * @param node The {@link Object} to check
    * @return True if the given object is an instance of {@link ISEGroupable} and {@link ISEGroupable#isGroupable()}
    * False otherwise.
    */
   public static boolean canBeGrouped(Object node) {
      return node instanceof ISEGroupable && ((ISEGroupable) node).isGroupable();// && node instanceof ISEDMethodCall;
   }
   
   /**
    * Returns the next {@link ISENode} for {@link NodeUtil#getSortedBCs(ISEGroupable)}.
    * @param node The current position/node in the group.
    * @param start The {@link ISENode} to start from.
    * @param groupEndReached True if a group endnode is reached, False otherwise.
    * @return The next {@link ISENode} in the group.
    * @throws DebugException Occured Exception.
    */
   private static ISENode determineNextNode(ISENode node, ISENode start, boolean groupEndReached) throws DebugException {
      ISENode[] children = node.getChildren();

      if (!ArrayUtil.isEmpty(children) && !groupEndReached) {
         return children[0];
      }
      else {
         ISENode parent = node.getParent();
         // Search next debug node
         while (parent instanceof ISENode) {
            ISENode[] parentChildren = parent.getChildren();
            int nodeIndex = ArrayUtil.indexOf(parentChildren, node);
            if (nodeIndex < 0) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Parent node \"" + parent + "\" does not contain child \"" + node + "."));
            }
            if (nodeIndex + 1 < parentChildren.length) {
               if (parentChildren[nodeIndex] != start) {
                  return parentChildren[nodeIndex + 1];
               }
               else {
                  return null;
               }
            }
            else {
               if (parentChildren[parentChildren.length - 1] != start) {
                  node = parent;
                  parent = parent.getParent(); // Continue search on parent without recursive call!
               }
               else {
                  return null;
               }
            }
         }
         
         return null;
      }
   }
}