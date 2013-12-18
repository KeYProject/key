package de.uka.ilkd.key.logic.label;

import java.util.List;

/**
 * A factory for creating {@link SymbolicExecutionTermLabel} objects.
 */
public class SymbolicExecutionTermLabelFactory implements TermLabelFactory<SymbolicExecutionTermLabel> {
    /**
     * {@inheritDoc}
     *
     * <p>
     * This method accepts single arguments which can be parsed as an integer.
     */
    @Override
    public SymbolicExecutionTermLabel parseInstance(List<String> parameters) throws TermLabelException {
        if (parameters == null || parameters.size() != 1) {
            throw new TermLabelException("Label " + SymbolicExecutionTermLabel.NAME +
                    " requires exactly one Integer-Parameter with its ID.");
        }
        Integer val;
        try {
            val = Integer.valueOf(parameters.get(0));
        } catch (NumberFormatException e) {
            throw new TermLabelException("Label " + SymbolicExecutionTermLabel.NAME +
                    " requires exactly one Integer-Parameter with its ID.", e);
        }

        return new SymbolicExecutionTermLabel(val);
    }
}
