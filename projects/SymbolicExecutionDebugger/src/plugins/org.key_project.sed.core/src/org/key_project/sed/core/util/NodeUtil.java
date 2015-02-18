package org.key_project.sed.core.util;

import java.util.LinkedList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDGroupable;
import org.key_project.util.java.ArrayUtil;

/**
 * Provides static methods for {@link ISEDDebugNode} for
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
    * Returns the parent node of the given {@link ISEDDebugNode}.
    * If the given {@link ISEDDebugNode} end a collapsed group it will
    * return the specific {@link ISEDBranchCondition}.
    * @param node The {@link ISEDDebugNode} to get the parent for.
    * @return The parent {@link ISEDDebugNode} of the given node.
    * @throws DebugException Occurred Exception.
    */
   public static ISEDDebugNode getParent(ISEDDebugNode node) throws DebugException {
      if(!ArrayUtil.isEmpty(node.getGroupStartConditions())) {
         ISEDBranchCondition bc = node.getInnerMostVisibleGroupStartCondition();

         if(canBeGrouped(bc.getParent()) && ((ISEDGroupable)bc.getParent()).isCollapsed()) {
            return bc;
         }  
      }

      return node.getParent();
   }
   
   /**
    * Returns all children of the given {@link ISEDDebugNode}. If
    * {@link NodeUtil#canBeGrouped(Object)} and {@link ISEDGroupable#isCollapsed()}
    * are true it will return all {@link ISEDBranchConditions} to the end nodes sorted
    * from left to right.
    * @param node The {@link ISEDDebugNode} to get the children for.
    * @return The sorted children as {@link ISEDBranchCondition}-Array. 
    * @throws DebugException Occured Exception.
    */
   public static ISEDDebugNode[] getChildren(ISEDDebugNode node) throws DebugException {
      if(canBeGrouped(node)) {
         ISEDGroupable groupStart = (ISEDGroupable) node;
         if(groupStart.isCollapsed()) {
            return getSortedBCs(groupStart);
         }
      }

      return node.getChildren();
   }
   
   /**
    * Returns the sorted {@link ISEDBranchCondition}s of the given {@link ISEDGroupable}.
    * @param groupStart The {@link ISEDGroupable} to get the {@link ISEDBranchCondition}s for.
    * @return The sorted {@link ISEDBranchCondition}s.
    * @throws DebugException Occured Exception.
    */
   public static ISEDBranchCondition[] getSortedBCs(ISEDGroupable groupStart) throws DebugException {
      LinkedList<ISEDDebugNode> orderedBCs = new LinkedList<ISEDDebugNode>();
      
      ISEDDebugNode next = determineNextNode((ISEDDebugNode) groupStart, (ISEDDebugNode) groupStart, false);
      while (next != null)
      {
         boolean groupEndReached = false;
         
         ISEDDebugNode bc = next.getGroupStartCondition((ISEDDebugNode) groupStart);
         
         if(bc != null) {
            orderedBCs.add(bc);
            groupEndReached = true;
         }
         
         next = determineNextNode(next, (ISEDDebugNode) groupStart, groupEndReached);
      }
   
      return orderedBCs.toArray(new ISEDBranchCondition[orderedBCs.size()]);
   }
   
   /**
    * Returns the startnode of the group in which the given {@link ISEDDebugNode} lies.   
    * @param node The {@link ISEDDebugNode} to get the group startnode for.
    * @return The {@link ISEDGroupable} of the group of the given {@link ISEDDebugNode}.
    * @throws DebugException Occured Exception.
    */
   public static ISEDGroupable getGroupStartNode(ISEDDebugNode node) throws DebugException {
      
      if(node == null) {
         return null;
      }

      if(!ArrayUtil.isEmpty(node.getGroupStartConditions())) {
         return (ISEDGroupable) getParent(node.getInnerMostVisibleGroupStartCondition());
      }
      
      int currentPosition = -1;
      
      ISEDDebugNode parent = getParent(node);
      while(parent != null) {
         if(canBeGrouped(parent)) {
            currentPosition++;
         }
         else if(!ArrayUtil.isEmpty(parent.getGroupStartConditions())) {
            int index = ArrayUtil.indexOf(parent.getGroupStartConditions(), parent.getInnerMostVisibleGroupStartCondition());
            currentPosition -= index + 1;
         }

         if(currentPosition == 0) {
            return (ISEDGroupable) parent;
         }
         
         parent = getParent(parent);
      }

      return null;
   }
   
   /**
    * Determines if the given {@link Object} is an instance of {@link ISEDGroupable} and
    * {@link ISEDGroupable#isGroupable()}.
    * @param node The {@link Object} to check
    * @return True if the given object is an instance of {@link ISEDGroupable} and {@link ISEDGroupable#isGroupable()}
    * False otherwise.
    */
   public static boolean canBeGrouped(Object node) {
      return node instanceof ISEDGroupable && ((ISEDGroupable) node).isGroupable();// && node instanceof ISEDMethodCall;
   }
   
   /**
    * Returns the next {@link ISEDDebugNode} for {@link NodeUtil#getSortedBCs(ISEDGroupable)}.
    * @param node The current position/node in the group.
    * @param start The {@link ISEDDebugNode} to start from.
    * @param groupEndReached True if a group endnode is reached, False otherwise.
    * @return The next {@link ISEDDebugNode} in the group.
    * @throws DebugException Occured Exception.
    */
   private static ISEDDebugNode determineNextNode(ISEDDebugNode node, ISEDDebugNode start, boolean groupEndReached) throws DebugException {
      ISEDDebugNode[] children = node.getChildren();

      if (!ArrayUtil.isEmpty(children) && !groupEndReached) {
         return children[0];
      }
      else {
         ISEDDebugNode parent = node.getParent();
         // Search next debug node
         while (parent instanceof ISEDDebugNode) {
            ISEDDebugNode[] parentChildren = parent.getChildren();
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