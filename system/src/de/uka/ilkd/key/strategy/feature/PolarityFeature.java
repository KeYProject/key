package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * Computes the polarity of a term 
 */
public class PolarityFeature implements Feature {
	
	public static final Feature POSITIVE_POLARITY = new PolarityFeature(true);
	public static final Feature NEGATIVE_POLARITY = new PolarityFeature(false);
	
	private final int checkedForPolarity; 
		
	public PolarityFeature(boolean b) {
		this.checkedForPolarity = b ? 1 : -1;
	}

	@Override
	public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
		int polarity = pos.isInAntec() ? -1 : 1;
		Term formula = pos.constrainedFormula().formula();
		
		PIOPathIterator it = pos.iterator();
		loop:
			while (it.hasNext()) {
			final int termPos = it.next();
			formula = it.getSubTerm();
			
			if (formula.sort() != Sort.FORMULA) {
				break;
			} else if (formula.op() == Junctor.NOT) {
				polarity = polarity * -1;				
			} else if (formula.op() == Junctor.IMP) {
				if (termPos == 0) {
					polarity = polarity * -1;									
				}
			} else if (formula.op() instanceof IfThenElse || 
					   formula.op() instanceof IfExThenElse) { 				
				switch (termPos) {
					case 0: polarity = 0; 
							break loop;
					default: 
							break; 
				}
			} else if (formula.op() == Equality.EQV) {
				polarity = 0;
				break loop;
			} 			
		}
		return polarity * checkedForPolarity > 0 ? LongRuleAppCost.ZERO_COST : TopRuleAppCost.INSTANCE;
	}

}
