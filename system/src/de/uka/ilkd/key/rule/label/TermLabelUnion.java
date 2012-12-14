package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.rule.MatchConditions;

/**
 * A term label which represents the union of term labels of its parameters.  
 */
public class TermLabelUnion extends TermLabelOperation {

    /**
     * creates an instance which represents the union of the termlabels of its parameters
     */
    TermLabelUnion(ITermLabel left,ITermLabel right) {
        super("union", new ITermLabel[]{left, right});
    }

    @Override
    public ImmutableArray<ITermLabel> evaluate(MatchConditions cond,
            Services services) {
        return null;
    }
        
}
