package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.logic.AutoSpecTermLabel;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;

public class AutoSpecTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
    /**
     * The only instance of this class.
     */
    public static final AutoSpecTermLabelInstantiator INSTANCE = new AutoSpecTermLabelInstantiator();

    /**
     * Constructor to forbid multiple instances.
     */
    private AutoSpecTermLabelInstantiator() {
    }

    @Override
    public String getName() {
        return AutoSpecTermLabel.NAME.toString();
    }

    @Override
    protected ITermLabel getTermLabel(Term applicationTerm) {
        return AutoSpecTermLabel.INSTANCE;
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