package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.label.TermLabelOperationsInterpreter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * A term label which represents the intersection of term labels of its parameters.  
 */
public class TermLabelIntersection extends TermLabelOperation {

    /**
     * creates an instance which represents the intersection of the term labels of its parameters
     */
    TermLabelIntersection(ITermLabel left,ITermLabel right) {
        super("\\cap", new ITermLabel[]{left, right});
    }

    @Override
    public ImmutableArray<ITermLabel> evaluate(SVInstantiations svInst,
            Services services) {
        ImmutableArray<ITermLabel> left = getChild(0) instanceof TermLabelOperation ? ((TermLabelOperation) getChild(0))
                .evaluate(svInst, services) : new ImmutableArray<ITermLabel>(
                getChild(0));
        ImmutableArray<ITermLabel> right = getChild(1) instanceof TermLabelOperation ? ((TermLabelOperation) getChild(1))
                .evaluate(svInst, services) : new ImmutableArray<ITermLabel>(
                getChild(1));
        return TermLabelOperationsInterpreter.intersection(left, right);
    }
        
}
