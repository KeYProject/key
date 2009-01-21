package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class LocalScopeSpec extends ScopeSpec {
    
    public LocalScopeSpec() {
        super(new Name("#localScopeSpec"), 1);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        return calculate(term, svInst, services, true);
    }
    
}
