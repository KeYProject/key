package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.TermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.label.TermLabelInstantiator;

public final class SimpleTermLabel implements TermLabel {

    private final Name name;
    private final TermLabelInstantiator instantiator;

    public SimpleTermLabel(Name name, TermLabelInstantiator worker) {
        this.name = name;
        this.instantiator = worker;
    }

    @Override 
    public Name name() {
        return name;
    }

    @Override 
    public Object getChild(int i) {
        throw new IndexOutOfBoundsException();
    }

    @Override 
    public int getChildCount() {
        return 0;
    }

    @Override 
    public String toString() {
        return name.toString();
    }

    @Override 
    public boolean equals(Object obj) {
        if (obj instanceof SimpleTermLabel) {
            SimpleTermLabel other = (SimpleTermLabel) obj;
            return name.equals(other.name);
        }
        return false;
    }

    @Override 
    public int hashCode() {
        return name.hashCode();
    }

    @Override 
    public TermLabelInstantiator getInstantiator() {
        return instantiator;
    }

}
