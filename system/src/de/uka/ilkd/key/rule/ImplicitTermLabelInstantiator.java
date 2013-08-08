package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.logic.ImplicitTermLabel;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;

public class ImplicitTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
    /**
     * The only instance of this class.
     */
    public static final ImplicitTermLabelInstantiator INSTANCE = new ImplicitTermLabelInstantiator();

    /**
     * Constructor to forbid multiple instances.
     */
    private ImplicitTermLabelInstantiator() {
    }

    @Override
    public String getName() {
        return ImplicitTermLabel.NAME.toString();
    }

    @Override
    protected ITermLabel getTermLabel(Term applicationTerm) {
        return ImplicitTermLabel.INSTANCE;
    }

    @Override
    public List<ITermLabel> updateLabels(Term tacletTerm,
                                         PosInOccurrence applicationPosInOccurrence,
                                         Term termToUpdate,
                                         Rule rule,
                                         Goal goal) {
        return keepLabels(termToUpdate);
    }
}