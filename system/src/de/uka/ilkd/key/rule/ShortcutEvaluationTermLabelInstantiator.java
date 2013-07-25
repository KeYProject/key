package de.uka.ilkd.key.rule;
import java.util.List;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ShortcutEvaluationTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractSymbolicExecutionInstantiator;
import de.uka.ilkd.key.rule.Rule;


public class ShortcutEvaluationTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
    /**
     * The only instance of this class.
     */
    public static final ShortcutEvaluationTermLabelInstantiator INSTANCE =
            new ShortcutEvaluationTermLabelInstantiator();

    /**
     * Constructor to forbid multiple instances.
     */
    private ShortcutEvaluationTermLabelInstantiator() {
    }

    @Override
    public String getName() {
        return ShortcutEvaluationTermLabel.NAME.toString();
    }

    @Override
    protected ITermLabel getTermLabel(Term applicationTerm) {
        return ShortcutEvaluationTermLabel.INSTANCE;
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