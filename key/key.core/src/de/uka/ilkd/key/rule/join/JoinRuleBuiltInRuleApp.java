package de.uka.ilkd.key.rule.join;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.Pair;

/**
 * Rule application class for join rule applications. Is complete iff
 * the joinPartners field as well as the concrete join rule to be used
 * have been set by the corresponding setter function.
 * 
 * @author Dominic Scheurer
 */
public class JoinRuleBuiltInRuleApp extends AbstractBuiltInRuleApp {
    
    private ImmutableList<Pair<Goal, PosInOccurrence>> joinPartners = null;
    private JoinProcedure concreteRule = null;

	public JoinRuleBuiltInRuleApp(BuiltInRule builtInRule,
            PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    protected JoinRuleBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts) {
        super(rule, pio, ifInsts);
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return null;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        return this;
    }
    
    @Override
    public boolean complete() {
        return joinPartners != null && concreteRule != null;
    }

    public ImmutableList<Pair<Goal, PosInOccurrence>> getJoinPartners() {
        return joinPartners;
    }
    
    public void setJoinPartners(ImmutableList<Pair<Goal, PosInOccurrence>> joinPartners) {
        this.joinPartners = joinPartners;
    }

    public JoinProcedure getConcreteRule() {
		return concreteRule;
	}

	public void setConcreteRule(JoinProcedure concreteRule) {
		this.concreteRule = concreteRule;
	}

}
