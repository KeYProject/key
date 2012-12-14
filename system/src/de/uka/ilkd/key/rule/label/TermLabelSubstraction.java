package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.rule.MatchConditions;

/**
 * A term label which represents the set difference of term labels of its parameters.
 * The represented set of labels is those of the first parameter minus   
 */
public class TermLabelSubstraction extends TermLabelOperation {

    /**
     * creates an instance which represents the set difference of the termlabels of its parameters
     */
    TermLabelSubstraction(ITermLabel left, ITermLabel right) {
        super("minus", new ITermLabel[]{left, right});
    }

    @Override
    public ImmutableArray<ITermLabel> evaluate(MatchConditions cond,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }
        
}
