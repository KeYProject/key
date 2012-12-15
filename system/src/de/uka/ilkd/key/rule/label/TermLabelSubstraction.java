package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.label.TermLabelOperations;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * A term label which represents the set difference of term labels of its parameters.
 * The represented set of labels is those of the first parameter minus   
 */
public class TermLabelSubstraction extends TermLabelOperation {

    /**
     * creates an instance which represents the set difference of the termlabels of its parameters
     */
    TermLabelSubstraction(ITermLabel left, ITermLabel right) {
        super("\\sub", new ITermLabel[]{left, right});
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
        return TermLabelOperations.sub(left, right);
    }
        
}
