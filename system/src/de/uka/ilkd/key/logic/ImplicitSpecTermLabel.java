package de.uka.ilkd.key.logic;

/**
 * Label attached to a term which is specified implicitly (by the JML specification).
 */
public class ImplicitSpecTermLabel implements ITermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("ImplicitSpec");

    /**
     * The only instance of this class.
     */
    public static ImplicitSpecTermLabel INSTANCE = new ImplicitSpecTermLabel();

    /**
     * Constructor to forbid multiple instances.
     */
    private ImplicitSpecTermLabel() {
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