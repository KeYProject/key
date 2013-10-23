package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.label.TermLabelException;
import de.uka.ilkd.key.logic.label.TermLabelFactory;

public class SymbolicExecutionTermLabelFactory implements TermLabelFactory<SymbolicExecutionTermLabel> {

    @Override 
    public Name name() {
        return SymbolicExecutionTermLabel.NAME;
    }

    @Override 
    public SymbolicExecutionTermLabel parse(List<String> parameters) throws TermLabelException {
        if (parameters == null || parameters.size() != 1) {
            throw new TermLabelException("Label " + name() +
                    " requires exactly one Integer-Parameter with its ID.");
        }
        Integer val;
        try {
            val = Integer.valueOf(parameters.get(0));
        } catch (NumberFormatException e) {
            throw new TermLabelException("Label " + name() +
                    " requires exactly one Integer-Parameter with its ID.", e);
        }

        return new SymbolicExecutionTermLabel(val);
    }

    @Override 
    public SymbolicExecutionTermLabel create(List<?> parameters)
            throws TermLabelException {
        
        if (parameters == null || parameters.size() != 1) {
            throw new TermLabelException("Label " + name() +
                    " requires exactly one Integer-Parameter with its ID.");
        }
        
        Object arg = parameters.get(0);
        if (arg instanceof Number) {
            Number number = (Number) arg;
            return new SymbolicExecutionTermLabel(number.intValue());
        } else {
            throw new TermLabelException("Label " + name() +
                    " requires exactly one Integer-Parameter with its ID.");
        }
    }
}
