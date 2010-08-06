package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.BinaryTacletAppFeature;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

public class IntroducedSymbolBy extends BinaryTacletAppFeature {

    
    private final Name ruleSetName;
    private final Name schemaVar;
    private final ProjectionToTerm term;

    public static Feature create(ProjectionToTerm termWithTopLevelOpToCheck, 
	   	String ruleSetName, String schemaVar) {
	return new IntroducedSymbolBy(termWithTopLevelOpToCheck, 
		new Name(ruleSetName), new Name(schemaVar));
    }
    
    protected IntroducedSymbolBy(ProjectionToTerm termWithTopLevelOpToCheck, 
	   	Name ruleSetName, Name schemaVar) {
	this.term = termWithTopLevelOpToCheck;
	this.ruleSetName = ruleSetName;
	this.schemaVar = schemaVar;
    }
    
    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
	final Node root = goal.proof().root();
	
	Node n = goal.node();
	while (n != root) {	    
	    final RuleApp ra = n.getAppliedRuleApp();
	    if (ra instanceof TacletApp) {
		final TacletApp ta = (TacletApp) ra;
		if (ta.taclet().getRuleSets().contains(new RuleSet(ruleSetName))) {
		    final Object svInstValue = ta.instantiations().lookupValue(schemaVar);
		    if ( svInstValue instanceof Term ) {
			return term.toTerm(app, pos, goal).op() == ((Term)svInstValue).op();
		    }
		}
	    }	    	    
	    n = n.parent();
	}
	
	return false;
    }

}
