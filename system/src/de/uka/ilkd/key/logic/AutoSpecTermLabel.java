package de.uka.ilkd.key.logic;

public class AutoSpecTermLabel implements ITermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("AutoSpec");

    /**
     * The only instance of this class.
     */
    public static AutoSpecTermLabel INSTANCE = new AutoSpecTermLabel();

    /**
     * Constructor to forbid multiple instances.
     */
    private AutoSpecTermLabel() {
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