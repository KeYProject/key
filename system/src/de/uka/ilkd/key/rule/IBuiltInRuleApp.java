package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

public interface IBuiltInRuleApp extends RuleApp {

    public abstract RuleApp tryToInstantiate(Goal goal);

    public abstract boolean isSufficientlyComplete();

    public abstract ImmutableList<PosInOccurrence> ifInsts();

    public abstract IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts);

}
