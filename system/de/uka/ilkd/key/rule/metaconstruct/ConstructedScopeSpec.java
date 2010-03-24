package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ConstructedScopeSpec extends ScopeSpec {

    public ConstructedScopeSpec() {
        super(new Name("#constructedScopeSpec"), 1);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        return calculate(term, svInst, services, false);
    }
    
}
