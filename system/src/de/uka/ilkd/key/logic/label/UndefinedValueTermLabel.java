package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;

/**
 * Label attached to a term which denotes an undefined value.
 *
 * @author Michael Kirsten
 */
public class UndefinedValueTermLabel implements ITermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("undef");

    /**
     * The only instance of this class.
     */
    public static UndefinedValueTermLabel INSTANCE = new UndefinedValueTermLabel();

    /**
     * Constructor to forbid multiple instances.
     */
    private UndefinedValueTermLabel() {
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