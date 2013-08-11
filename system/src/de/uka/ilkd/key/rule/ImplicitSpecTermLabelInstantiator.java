package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.logic.ImplicitSpecTermLabel;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;

public class ImplicitSpecTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
    /**
     * The only instance of this class.
     */
    public static final ImplicitSpecTermLabelInstantiator INSTANCE = new ImplicitSpecTermLabelInstantiator();

    /**
     * Constructor to forbid multiple instances.
     */
    private ImplicitSpecTermLabelInstantiator() {
    }

    @Override
    public String getName() {
        return ImplicitSpecTermLabel.NAME.toString();
    }

    @Override
    protected ITermLabel getTermLabel(Term applicationTerm) {
        return ImplicitSpecTermLabel.INSTANCE;
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