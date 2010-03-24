package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class AtLocalScope extends MetaScopeAnnotation {

    public AtLocalScope() {
        super(new Name("#atLocalScope"), 1);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        MethodBodyStatement mb = getMethodBodyStatement(term.sub(0));
        boolean ls = mb.getMethodReference().localScope();
        return termFactory.createJunctorTerm(ls ? Op.TRUE : Op.FALSE);
    }

}
