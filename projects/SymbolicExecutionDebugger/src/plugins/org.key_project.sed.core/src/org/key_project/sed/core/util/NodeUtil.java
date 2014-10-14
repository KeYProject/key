package org.key_project.sed.core.util;

import java.util.LinkedList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.util.java.ArrayUtil;

public final class NodeUtil {
   
   private NodeUtil() {
   }
   
   public static ISEDDebugNode getParent(ISEDDebugNode node) throws DebugException {
      if(node instanceof ISEDBaseMethodReturn)
      {
         ISEDBranchCondition bc = ((ISEDBaseMethodReturn)node).getMethodReturnCondition();
         
         if(bc != null) {
            if(((ISEDMethodCall) bc.getParent()).isCollapsed()) {
               return bc;
            }
         }
      }

      return node.getParent();
   }
   
   public static ISEDDebugNode[] getChildren(ISEDDebugNode node) throws DebugException {
      return getChildren(node, false);
   }
   
   public static ISEDDebugNode[] getChildren(ISEDDebugNode node, boolean sorted) throws DebugException {
      if(node instanceof ISEDMethodCall)
      {
         ISEDMethodCall mc = (ISEDMethodCall) node;
         if(mc.isCollapsed()){
            return sorted ? getSortedBCs(mc) : mc.getMethodReturnConditions();
         }
      }

      return node.getChildren();
   }
   
   public static ISEDBranchCondition[] getSortedBCs(ISEDMethodCall mc) throws DebugException {
      LinkedList<ISEDDebugNode> orderedBCs = new LinkedList<ISEDDebugNode>();
      
      ISEDDebugNode next = determineNextNode(mc, mc, false);
      while (next != null)
      {
         boolean methodReturnReached = false;
         
         if(next instanceof ISEDBaseMethodReturn)
         {
            ISEDBaseMethodReturn nextMR = (ISEDBaseMethodReturn) next; 
            ISEDDebugNode nextMC = nextMR.getCallStack()[0];
            if(nextMC.equals(mc)) {
               orderedBCs.add(nextMR.getMethodReturnCondition());
               methodReturnReached = true;
            }
         }
         
         next = determineNextNode(next, mc, methodReturnReached);
      }
      
      return orderedBCs.toArray(new ISEDBranchCondition[orderedBCs.size()]);
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
