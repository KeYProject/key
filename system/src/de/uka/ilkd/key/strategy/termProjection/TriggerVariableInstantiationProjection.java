package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;

public class TriggerVariableInstantiationProjection implements ProjectionToTerm  {

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert app.rule() instanceof Taclet;
        final Taclet t = (Taclet) app.rule();
        
        final SVInstantiationProjection instProj = 
                SVInstantiationProjection.create(t.getTrigger().getTriggerVar().name(),
                true);
        return instProj.toTerm(app, pos, goal);
    }

    
    
}
