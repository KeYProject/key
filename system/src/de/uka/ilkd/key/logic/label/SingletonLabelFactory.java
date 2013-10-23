package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermLabel;

public class SingletonLabelFactory<T extends TermLabel> implements TermLabelFactory<T> {

    private final T simpleLabel;

    public SingletonLabelFactory(T simpleLabel) {
        this.simpleLabel = simpleLabel;
    }

    @Override 
    public Name name() {
        return simpleLabel.name();
    }

    @Override 
    public T parse(List<String> arguments) throws TermLabelException {
        if (arguments.isEmpty()) {
            return simpleLabel;
        } else {
            throw new TermLabelException("Label " + name() + " does not expect arguments");
        }
    }

    @Override 
    public T create(List<?> parameters) throws TermLabelException {
        if (parameters.isEmpty()) {
            return simpleLabel;
        } else {
            throw new TermLabelException("Label " + name() + " does not expect arguments");
        }
    }

}
