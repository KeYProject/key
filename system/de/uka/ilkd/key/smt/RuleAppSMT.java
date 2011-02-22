package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;

public class RuleAppSMT implements RuleApp {

    SMTRule rule;
    private String title;
    
    
    
    public RuleAppSMT(Goal goal, String title) {
	rule = new SMTRule();
	this.title = title;
	goal.proof().env().getJustifInfo().addJustification(rule, new RuleJustification() {
	    
	    @Override
	    public boolean isAxiomJustification() {
		// TODO Auto-generated method stub
		return false;
	    }
	});
    }
    
    @Override
    public boolean complete() {
	return true;
    }

    @Override
    public Constraint constraint() {
	return Constraint.BOTTOM;
    }

    @Override
    public ImmutableList<Goal> execute(Goal goal, Services services) {

	goal.addAppliedRuleApp(this);	
	ImmutableList<Goal> list = ImmutableSLList.nil();
	list = list.append(goal);
	goal.proof().closeGoal(goal,Constraint.BOTTOM);
	
	return null;
    }

    @Override
    public PosInOccurrence posInOccurrence() {
	return null;
    }

    @Override
    public Rule rule() {

	return rule;
    }
    
    private class SMTRule implements BuiltInRule{
	private Name name = new Name("SMTRule");
	
	@Override
        public boolean isApplicable(Goal goal, PosInOccurrence pio,
                Constraint userConstraint) {
	    return false;
        }

	@Override
        public ImmutableList<Goal> apply(Goal goal, Services services,
                RuleApp ruleApp) {
	    return null;
        }

	@Override
        public String displayName() {
	    return title;
        }
	
	public String toString(){
	    return displayName();
	}

	@Override
        public Name name() {
	     return name;
        }
	
    }


    
}
