package de.uka.ilkd.key.rule.join;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.Pair;

/**
 * TODO: Document.
 * 
 * @author Dominic Scheurer
 */
public class JoinRuleBuiltInRuleApp extends AbstractBuiltInRuleApp {
    
    private ImmutableList<Pair<Goal, PosInOccurrence>> joinPartners = null;

    protected JoinRuleBuiltInRuleApp(BuiltInRule builtInRule,
            PosInOccurrence pio) {
        // TODO Auto-generated constructor stub
        super(builtInRule, pio);
    }

    protected JoinRuleBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts) {
        // TODO Auto-generated constructor stub
        super(rule, pio, ifInsts);
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        // TODO Auto-generated method stub
        return null;
    }
    
    @Override
    public boolean complete() {
        return joinPartners != null;
    }
    
    public void setJoinPartners(ImmutableList<Pair<Goal, PosInOccurrence>> joinPartners) {
        this.joinPartners = joinPartners;
    }

}
