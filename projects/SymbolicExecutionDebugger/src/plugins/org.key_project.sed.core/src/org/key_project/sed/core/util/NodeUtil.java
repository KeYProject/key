package org.key_project.sed.core.util;

import java.util.LinkedList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDGroupable;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.util.java.ArrayUtil;

public final class NodeUtil {
   
   private NodeUtil() {
   }
   
   public static ISEDDebugNode getParent(ISEDDebugNode node) throws DebugException {
      if(!ArrayUtil.isEmpty(node.getGroupStartConditions())) {
         ISEDBranchCondition bc = node.getInnerMostVisibleGroupStartCondition();
         if(((ISEDGroupable)bc.getParent()).isCollapsed()) {
            return bc;
         }
         
      }
//      if(node instanceof ISEDBaseMethodReturn)
//      {
//         ISEDBranchCondition bc = ((ISEDBaseMethodReturn)node).getMethodReturnCondition();
//         
//         if(bc != null) {
//            if(((ISEDMethodCall) bc.getParent()).isCollapsed()) {
//               return bc;
//            }
//         }
//      }

      return node.getParent();
   }
   
   public static ISEDDebugNode[] getChildren(ISEDDebugNode node) throws DebugException {
      return getChildren(node, false);
   }
   
   public static ISEDDebugNode[] getChildren(ISEDDebugNode node, boolean sorted) throws DebugException {
      if(node instanceof ISEDGroupable) {
         ISEDGroupable groupStart = (ISEDGroupable) node;
         if(groupStart.isCollapsed()) {
            return sorted ? getSortedBCs(groupStart) : groupStart.getGroupEndConditions();
         }
      }

      return node.getChildren();
   }
   
   public static ISEDBranchCondition[] getSortedBCs(ISEDGroupable groupStart) throws DebugException {
      LinkedList<ISEDDebugNode> orderedBCs = new LinkedList<ISEDDebugNode>();
      
      ISEDDebugNode next = determineNextNode((ISEDDebugNode) groupStart, (ISEDDebugNode) groupStart, false);
      while (next != null)
      {
         boolean methodReturnReached = false;
         
         if(!ArrayUtil.isEmpty(next.getGroupStartConditions())) {
            ISEDGroupable nodeGroupStart = getGroupStartNode(next);
            if(nodeGroupStart == groupStart) {
               orderedBCs.add(next.getGroupStartCondition((ISEDDebugNode) nodeGroupStart));
               methodReturnReached = true;
            }
         }
         
         next = determineNextNode(next, (ISEDDebugNode) groupStart, methodReturnReached);
      }
      
      return orderedBCs.toArray(new ISEDBranchCondition[orderedBCs.size()]);
   }
   
   public static ISEDGroupable getGroupStartNode(ISEDDebugNode node) throws DebugException {
      
      if(node == null) {
         return null;
      }
//      System.out.println("Node: " + node);
      if(!ArrayUtil.isEmpty(node.getGroupStartConditions())) {
//         for(ISEDBranchCondition bc : node.getGroupStartConditions())
//            System.out.println("Has? " + bc);
         return (ISEDGroupable) getParent(node.getInnerMostVisibleGroupStartCondition());
      }
      
      int currentPosition = -1;
      
      ISEDDebugNode parent = getParent(node);
      while(parent != null) {
         if(parent instanceof ISEDGroupable) {
            currentPosition++;
         }
         else if(!ArrayUtil.isEmpty(parent.getGroupStartConditions())) {
//            for(ISEDBranchCondition bc : parent.getGroupStartConditions())
//               System.out.println("ParentCond: " + bc);
            currentPosition -= parent.getGroupStartConditions().length;
         }

         if(currentPosition == 0) {
//            System.out.println("Return: " + parent);
            return (ISEDGroupable) parent;
         }
         
         parent = getParent(parent);
      }
//      System.out.println("Return null");
      return null;
   }
   
   public static boolean canBeGrouped(Object node) {
//      if(node instanceof ISEDLoopCondition)
//         System.out.println("Node: " + node + ", ?: " + ((ISEDGroupable) node).isGroupable());
      return node instanceof ISEDGroupable && ((ISEDGroupable) node).isGroupable();
   }
   
   private static ISEDDebugNode determineNextNode(ISEDDebugNode node, ISEDDebugNode start, boolean methodReturnReached) throws DebugException {
      ISEDDebugNode[] children = node.getChildren();

      if (!ArrayUtil.isEmpty(children) && !methodReturnReached) {
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
