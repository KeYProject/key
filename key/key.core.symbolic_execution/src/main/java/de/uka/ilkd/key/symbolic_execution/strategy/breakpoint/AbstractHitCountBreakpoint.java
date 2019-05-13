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

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Adds the hit count functionality to an {@link AbstractBreakpoint}.
 * @author Martin Hentschel
 */
public abstract class AbstractHitCountBreakpoint extends AbstractBreakpoint {
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
   private final Map<Integer, Boolean> hittedNodes = new HashMap<Integer, Boolean>();

   /**
    * Creates a new {@link AbstractHitCountBreakpoint}.
    * 
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param proof the {@link Proof} that will be executed and should stop
    * @param enabled flag if the Breakpoint is enabled
    */
   public AbstractHitCountBreakpoint(int hitCount, Proof proof, boolean enabled){
      super(proof, enabled);
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
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Proof proof, Node node) {
      return hitcountExceeded(node);
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
      if (this.hitCount != hitCount) {
         this.hitCount = hitCount;
         this.hitted = 0;
         hittedNodes.clear();
      }
   }
}