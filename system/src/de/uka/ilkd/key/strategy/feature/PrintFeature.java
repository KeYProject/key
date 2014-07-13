package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * For debugging purposes. Wraps a feature and prints the computed value 
 */
public class PrintFeature implements Feature {

   private final Feature f;
   private final String prefix;

   public PrintFeature(String prefix, Feature f) {
      this.f = f;
      this.prefix = prefix;
   }

   public PrintFeature(Feature f) {
      this("", f);
   }

   
   @Override
   public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
      RuleAppCost cost = f.compute(app, pos, goal);
      System.out.println(prefix + ":" + cost.toString() + ":" + (pos != null ? pos.subTerm() + ":" : "") + app.rule().name() );
      return cost;
   }
    
    
    
 }