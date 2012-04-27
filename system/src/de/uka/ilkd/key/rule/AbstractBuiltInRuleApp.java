package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

public abstract class AbstractBuiltInRuleApp implements RuleApp {

	protected BuiltInRule builtInRule;

	public abstract RuleApp replacePos(PosInOccurrence newPos);

	protected PosInOccurrence pio;
	protected ImmutableList<PosInOccurrence> ifInsts = ImmutableSLList.<PosInOccurrence>nil();

	public AbstractBuiltInRuleApp() {
		super();
	}

	/**
     * returns the rule of this rule application
     */
    @Override
    public BuiltInRule rule() {
    return builtInRule;
    }

	/**
     * returns the PositionInOccurrence (representing a SequentFormula and
     * a position in the corresponding formula) of this rule application
     */
    @Override
    public PosInOccurrence posInOccurrence() {
    return pio;
    }

	/** applies the specified rule at the specified position 
     * if all schema variables have been instantiated
     * @param goal the Goal where to apply the rule
     * @param services the Services encapsulating all java information
     * @return list of new created goals 
     */
    @Override
    public ImmutableList<Goal> execute(Goal goal, Services services) {
    goal.addAppliedRuleApp(this);	
    ImmutableList<Goal> result = builtInRule.apply(goal, services, this);
    if (result == null){
        goal.removeLastAppliedRuleApp();
        goal.node().setAppliedRuleApp(null);
    }
    return result;
    }

    public void setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
	assert ifInsts != null;
	this.ifInsts = ifInsts;
    }
    
    
    public ImmutableList<PosInOccurrence> ifInsts() {
	return ifInsts;
    }
    
	/** returns true if all variables are instantiated 
     * @return true if all variables are instantiated 
     */
    @Override
    public boolean complete() {
    	return true;
    }

	@Override
    public String toString() {
    return "BuiltInRule: " + rule().name() + " at pos " + pio.subTerm();
    }

}
