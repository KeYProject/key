package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Operator;

public class IsUpdateOperatorTF extends BinaryTermFeature {
    
    public static final TermFeature INSTANCE = new IsUpdateOperatorTF();

    private IsUpdateOperatorTF() {}

    public static TermFeature create(Operator op) {
        return new IsUpdateOperatorTF ( );
    }
    
    protected boolean filter(Term term) {
        return term.op () instanceof IUpdateOperator;
    }
}
