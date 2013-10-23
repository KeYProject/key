package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.label.TermLabelException;
import de.uka.ilkd.key.logic.label.TermLabelFactory;

/**
 * A factory for creating SymbolicExecutionTermLabel objects.
 */
class SymbolicExecutionTermLabelFactory implements TermLabelFactory<SymbolicExecutionTermLabel> {

    @Override 
    public Name name() {
        return SymbolicExecutionTermLabel.NAME;
    }

    /**
     * {@inheritDoc}
     * 
     * <p>
     * This method accepts single arguments which can be parsed as an integer.
     */
    @Override 
    public SymbolicExecutionTermLabel parseInstance(List<String> parameters) throws TermLabelException {
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

    /**
     * {@inheritDoc}
     * 
     * <p>
     * This method accepts single arguments which are of type {@link Number}.
     */
    @Override 
    public SymbolicExecutionTermLabel getInstance(List<?> parameters)
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
