package org.key_project.sed.core.util;

import java.util.LinkedList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDGroupable;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.util.java.ArrayUtil;

public final class NodeUtil {
   
   private NodeUtil() {
   }
   
   public static ISEDDebugNode getParent(ISEDDebugNode node) throws DebugException {
      if(!ArrayUtil.isEmpty(node.getGroupStartConditions())) {
         ISEDBranchCondition bc = node.getInnerMostVisibleGroupStartCondition();

         if(bc.getParent() instanceof ISEDGroupable && ((ISEDGroupable)bc.getParent()).isCollapsed()) {
            return bc;
         }  
      }

      return node.getParent();
   }
   
   public static ISEDDebugNode[] getChildren(ISEDDebugNode node) throws DebugException {
      if(canBeGrouped(node)) {
         ISEDGroupable groupStart = (ISEDGroupable) node;
         if(groupStart.isCollapsed()) {
            return getSortedBCs(groupStart);
         }
      }

      return node.getChildren();
   }
   
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
   
   public static ISEDGroupable getGroupStartNode(ISEDDebugNode node) throws DebugException {
      
      if(node == null) {
         return null;
      }

      if(!ArrayUtil.isEmpty(node.getGroupStartConditions())) {
         ISEDDebugNode n = node.getInnerMostVisibleGroupStartCondition();
//         System.out.println("Node: " + node + ", InnerMost: " + n + ", Parent: " + getParent(n) + ", Parent2: " + n.getParent());
         return (ISEDGroupable) getParent(node.getInnerMostVisibleGroupStartCondition());
      }
      
      int currentPosition = -1;
      
      ISEDDebugNode parent = getParent(node);
      while(parent != null) {
         if(canBeGrouped(parent)) {
            currentPosition++;
         }
         else if(!ArrayUtil.isEmpty(parent.getGroupStartConditions())) {
            currentPosition -= parent.getGroupStartConditions().length;
         }

         if(currentPosition == 0) {
            return (ISEDGroupable) parent;
         }
         
         parent = getParent(parent);
      }

      return null;
   }
   
   public static boolean canBeGrouped(Object node) {
      return node instanceof ISEDGroupable && ((ISEDGroupable) node).isGroupable();// && node instanceof ISEDMethodCall;
   }
   
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
