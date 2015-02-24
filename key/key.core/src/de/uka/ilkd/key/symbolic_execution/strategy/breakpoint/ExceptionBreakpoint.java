// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * This{@link ExceptionBreakpoint} represents an exception breakpoint and is responsible to tell the debugger to stop execution when the respective
 * breakpoint is hit.
 * 
 * @author Marco Drebing
 */
public class ExceptionBreakpoint extends AbstractHitCountBreakpoint {
   /**
    * The exception to watch for
    */
   private String exceptionName;
   
   /**
    * a list of nodes of the Symbolic Execution Tree whose children represent exceptions
    */
   private Set<Node> exceptionParentNodes;
   
   /**
    * a flag whether to watch for an uncaught exception
    */
   private boolean caught;
   
   /**
    * a flag whether to suspend on subclasses of the exception aswell
    */
   private boolean suspendOnSubclasses;
   
   /**
    * a flag to tell whether to stop at uncaught exceptions or not
    */
   private boolean uncaught;

   /**
    * Creates a new {@link AbstractHitCountBreakpoint}.
    * 
    * @param proof the {@link Proof} that will be executed and should stop
    * @param exceptionName the name of the exception to watch for
    * @param caught flag to tell if caught exceptions lead to a stop
    * @param uncaught flag to tell if uncaught exceptions lead to a stop
    * @param suspendOnSubclasses flag to tell if the execution should suspend on subclasses of the exception aswell
    * @param enabled flag if the Breakpoint is enabled
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    */
   public ExceptionBreakpoint(Proof proof, String exceptionName, boolean caught, boolean uncaught, boolean suspendOnSubclasses, boolean enabled, int hitCount){
      super(hitCount, proof, enabled);
      this.exceptionName = exceptionName;
      exceptionParentNodes = new HashSet<Node>();
      this.caught=caught;
      this.uncaught=uncaught;
      this.suspendOnSubclasses=suspendOnSubclasses;
   }
   
   /**
    * Checks if the given node is a parent of the other given node.
    * @param node The {@link Node} to start search in.
    * @param node The {@link Node} that is thought to be the parent.
    * @return true if the parent node is one of the nodes parents
    */
   public boolean isParentNode(Node node, Node parent) {
      if (node != null) {
         Node parentIter = node.parent();
         boolean result = false;
         while (parentIter != null && !result) {
            if (parentIter.equals(parent)) {
               result = true;
            }
            else {
               parentIter = parentIter.parent();
            }
         }
         return result;
      }
      else {
         return false;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Proof proof, Node node) {
      Node SETParent = SymbolicExecutionUtil.findParentSetNode(node);
      if(activeStatement!=null&&activeStatement instanceof Throw&&isEnabled()){
         Throw throwStatement = (Throw)activeStatement;
         for(int i = 0; i<throwStatement.getChildCount();i++){
            SourceElement childElement = throwStatement.getChildAt(i);
            if(childElement instanceof LocationVariable){
               LocationVariable locVar = (LocationVariable)childElement;
               if(locVar.getKeYJavaType().getSort().toString().equals(exceptionName)&&!exceptionParentNodes.contains(SETParent)){
                  exceptionParentNodes.add(SETParent);
                  return true;
               }else if(suspendOnSubclasses){
                  JavaInfo info = proof.getServices().getJavaInfo();
                  KeYJavaType kjt = locVar.getKeYJavaType();
                  ImmutableList<KeYJavaType> kjts = info.getAllSupertypes(kjt);
                  for(KeYJavaType kjtloc: kjts){
                     if(kjtloc.getSort().toString().equals(exceptionName)&&!exceptionParentNodes.contains(SETParent)){
                        exceptionParentNodes.add(SETParent);
                        return true;
                     }
                  }
               }
            }
         }
      }
      return false;
   }
   
   /**
    * @return the isCaught
    */
   public boolean isCaught() {
      return caught;
   }
   
   /**
    * @param isCaught the isCaught to set
    */
   public void setCaught(boolean isCaught) {
      this.caught = isCaught;
   }
   
   /**
    * @return the isUncaught
    */
   public boolean isUncaught() {
      return uncaught;
   }
   
   /**
    * @param isUncaught the isUncaught to set
    */
   public void setUncaught(boolean isUncaught) {
      this.uncaught = isUncaught;
   }
   
   /**
    * @return the suspendOnSubclasses
    */
   public boolean isSuspendOnSubclasses() {
      return suspendOnSubclasses;
   }
   
   /**
    * @param suspendOnSubclasses the suspendOnSubclasses to set
    */
   public void setSuspendOnSubclasses(boolean suspendOnSubclasses) {
      this.suspendOnSubclasses = suspendOnSubclasses;
   }
}