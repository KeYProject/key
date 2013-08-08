package de.uka.ilkd.key.logic;

/**
 * Label attached to a term which is specified implicitly (by the JML specification). 
 */
public class ImplicitTermLabel implements ITermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("ImplicitSpec");

    /**
     * The only instance of this class.
     */
    public static ImplicitTermLabel INSTANCE = new ImplicitTermLabel();

    /**
     * Constructor to forbid multiple instances.
     */
    private ImplicitTermLabel() {
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