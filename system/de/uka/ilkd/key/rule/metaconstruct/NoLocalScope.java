package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class NoLocalScope extends MetaScopeAnnotation {

    public NoLocalScope() {
        super(new Name("#noLocalScope"), 1);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        MethodBodyStatement mb = getMethodBodyStatement(term.sub(0));
        boolean nl = mb.getProgramMethod(services).getMethodDeclaration().noLocalScope();
        return termFactory.createJunctorTerm(nl ? Op.TRUE : Op.FALSE);
    }
    
}
