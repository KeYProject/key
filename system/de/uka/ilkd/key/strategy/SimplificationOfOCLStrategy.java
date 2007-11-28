// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.SumFeature;


/** 
 * Used for OCL Simplification.
 */
public class SimplificationOfOCLStrategy extends AbstractFeatureStrategy {
    
    static final int PHASE_1 = 1;
    static final int PHASE_2 = 2;
    static final int PHASE_3 = 3;
    private Feature simplRulesF;
    private Feature spec2iterateF;
    private Feature iterate2specF;   
    private Feature completeF;
    private int phase = PHASE_1;

    public SimplificationOfOCLStrategy(Proof proof) {
        super (proof);
        
        simplRulesF = ifHeuristics (new String[] {"ocl_simplify"}, -3000);
	spec2iterateF = ifHeuristics (new String[] {"ocl_spec2iterate"}, -3000);
        iterate2specF = ifHeuristics (new String[] {"ocl_iterate2spec"}, -2000);
        completeF = SumFeature.createSum (new Feature[] {simplRulesF, spec2iterateF, iterate2specF});
    }
    
    public Name name () {
        return new Name("SimplificationOfOCLStrategy");
    }


    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     * 
     * @return the cost of the rule application expressed as a
     *         <code>RuleAppCost</code> object.
     *         <code>TopRuleAppCost.INSTANCE</code> indicates that the rule
     *         shall not be applied at all (it is discarded by the strategy).
     */
    public RuleAppCost computeCost (RuleApp app, PosInOccurrence pio, Goal goal) {
        return completeF.compute(app, pio, goal);
    }

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is
     * called immediately before a rule is really applied
     * @return true iff the rule should be applied, false otherwise
     */
    public boolean isApprovedApp (RuleApp app, PosInOccurrence pio, Goal goal) {
	//The phase in which the simplification is performed
	if (phase == PHASE_1) {
	    //If no more simplification rules are applicable then give the
	    //highest priority to the "iterate2something" rules and indicate
	    //that the simplification phase is over
	    if (simplRulesF.compute(app, pio, goal).compareTo(LongRuleAppCost.ZERO_COST) == 0
		&& spec2iterateF.compute(app, pio, goal).compareTo(LongRuleAppCost.ZERO_COST) == 0) {
		spec2iterateF = ifHeuristics (new String[] {"ocl_spec2iterate"}, -1000);
		completeF = SumFeature.createSum (new Feature[] {simplRulesF, spec2iterateF, iterate2specF});
		phase = PHASE_2;
	    }
	} 

	//The phase in which all "iterate" constructs are translated back to 
	//more specialized collection operations
	else if (phase == PHASE_2) {
	    //If no more "iterate2something" rules are applicable then stop the 
	    //automatic rule application
	    if (iterate2specF.compute(app, pio, goal).compareTo(LongRuleAppCost.ZERO_COST) == 0) {
		//completeF = ConstFeature.createConst(TopRuleAppCost.INSTANCE);
		phase = PHASE_3;
		return false;
	    }
	}

	//The "listening" phase. If any rules are applied manually or if "Goal Back" is
	//pressed so that a simplification rule are again applicable, then reset 
	//everything and go back to pahse 1.
	else {
	    if (simplRulesF.compute(app, pio, goal).compareTo(LongRuleAppCost.ZERO_COST) != 0) {
		simplRulesF = ifHeuristics (new String[] {"ocl_simplify"}, -3000);
		spec2iterateF = ifHeuristics (new String[] {"ocl_spec2iterate"}, -3000);
		iterate2specF = ifHeuristics (new String[] {"ocl_iterate2spec"}, -2000);
		completeF = SumFeature.createSum (new Feature[] {simplRulesF, spec2iterateF, iterate2specF});
		phase = PHASE_1;
	    } else {
		return false;
	    }
	}
        return !(completeF.compute(app, pio, goal) instanceof TopRuleAppCost);
    }
    
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return TopRuleAppCost.INSTANCE;
    }    

    public static class Factory extends StrategyFactory {
        public Factory () {     
        }
        
        public Strategy create (Proof proof, StrategyProperties strategyProperties) {
            return new SimplificationOfOCLStrategy(proof);
        }
        
        public Name name () {
            return new Name("SimplificationOfOCLStrategy");
        }
    }
}
