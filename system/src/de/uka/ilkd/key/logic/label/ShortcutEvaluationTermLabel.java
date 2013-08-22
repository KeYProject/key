package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;

/**
 * Label attached to a term with the logical operator '||' or '&&' to
 * distinguish from '|' or '&'. 
 */
public class ShortcutEvaluationTermLabel implements ITermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("Shortcut");

    /**
     * The only instance of this class.
     */
    public static ShortcutEvaluationTermLabel INSTANCE = new ShortcutEvaluationTermLabel();

    /**
     * Constructor to forbid multiple instances.
     */
    private ShortcutEvaluationTermLabel() {
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public Object getChild(int i) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    public String toString() {
        return NAME.toString();
    }
}