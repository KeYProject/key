package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;

/**
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
public class SpecNameLabel implements TermLabel {
    private static final Name NAME = new Name("name");

    public final String name;

    public SpecNameLabel(String name) {
        this.name = name;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public Object getChild(int i) {
        if (i == 0) return name;
        throw new IllegalArgumentException("index out of bounds");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    public String getName() {
        return name;
    }
}
