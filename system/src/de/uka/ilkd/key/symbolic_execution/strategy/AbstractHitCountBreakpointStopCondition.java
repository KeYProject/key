// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

public abstract class AbstractHitCountBreakpointStopCondition extends
      AbstractBreakpointStopCondition {
   

   
   /**
    * The HitCount of the Breakpoint (set by user).
    */
   private int hitCount;
   
   /**
    * Counter for how often the Breakpoint was hit.
    */
   private int hitted = 0;

   /**
    * Map to save the nodes that already have been reached, so nodes are not counted twice for the hitcount
    */
   private Map<Integer, Boolean> hittedNodes;


   /**
    * Creates a new {@link AbstractHitCountBreakpointStopCondition}.
    * 
    * @param classPath the path of the class the associated Breakpoint lies within
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param environment the environment the that the proof that should be stopped is working in
    * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located at
    * @param proof the {@link Proof} that will be executed and should stop
    * @param parentCondition a {@link CompoundStopCondition} containing this {@link LineBreakpointStopCondition} and all other {@link LineBreakpointStopCondition} the associated {@link Proof} should use
    * @param condition the condition as given by the user
    * @param enabled flag if the Breakpoint is enabled
    * @param containerType the type of the element containing the breakpoint
    */
   public AbstractHitCountBreakpointStopCondition(String classPath, int hitCount, KeYEnvironment<?> environment,
         IProgramMethod pm, Proof proof, CompoundStopCondition parentCondition,
         boolean enabled, KeYJavaType containerType){
      super(classPath, environment, pm, proof, parentCondition, enabled);
      hittedNodes = new HashMap<Integer, Boolean>();
      this.hitCount = hitCount;
   }

   
   /**
    * Checks if the Hitcount is exceeded for the given {@link JavaLineBreakpoint}.
    * If the Hitcount is not exceeded the hitted counter is incremented, otherwise its set to 0.
    * 
    * @return true if the Hitcount is exceeded or the {@link JavaLineBreakpoint} has no Hitcount.
    */
   protected boolean hitcountExceeded(Node node){
      if (!(hitCount == -1)) {
         if(!hittedNodes.containsKey(node.serialNr())){
            if (hitCount == hitted + 1) {
               hitted=0;
               hittedNodes.put(node.serialNr(), Boolean.TRUE);
               return true;
            }
            else {
               hittedNodes.put(node.serialNr(), Boolean.FALSE);
               hitted++;
            }
         }else {
            return hittedNodes.get(node.serialNr());
         }
      }
      else {
         return true;
      }
      return false;
   }
   
   @Override
   protected boolean breakpointHit(int line, String path, RuleApp ruleApp, Proof proof, Node node) throws ProofInputException {
      return super.breakpointHit(line, path, ruleApp, proof, node)&&hitcountExceeded(node);
   }

   /**
    * Returns the hitCount of the associated Breakpoint.
    * @return the hitCount of the associated Breakpoint
    */
   public int getHitCount() {
      return hitCount;
   }
   
   /**
    * Set the hitCount to the new value
    * @param hitCount the new value
    */
   public void setHitCount(int hitCount) {
      this.hitCount = hitCount;
   }

}
