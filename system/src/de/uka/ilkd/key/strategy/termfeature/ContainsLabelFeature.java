package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;

public class ContainsLabelFeature extends BinaryFeature {

   private final ITermLabel label;


   public ContainsLabelFeature(ITermLabel label) {
      this.label = label;
   }
   
  

   @Override
   protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
      return pos != null && pos.subTerm().containsLabel(label);
   }

}
