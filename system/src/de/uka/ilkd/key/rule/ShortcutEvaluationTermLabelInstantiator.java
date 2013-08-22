package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ShortcutEvaluationTermLabel;
import de.uka.ilkd.key.rule.AbstractSymbolicExecutionInstantiator;


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
}