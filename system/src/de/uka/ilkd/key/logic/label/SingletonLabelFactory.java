package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.Name;

/**
 * A factory for creating singleton term label.
 * 
 * <p>
 * The resulting factory does not accept arguments for the builder methods and
 * always returns a fixed term level value.
 * 
 * @param <T>
 *            the type of the wrapped term label can be narrowed.
 */
final class SingletonLabelFactory<T extends TermLabel> implements TermLabelFactory<T> {

    /**
     * The label around which the factory is built.
     */
    private final T simpleLabel;

    /**
     * Instantiates a new singleton label factory for a label.
     * 
     * @param simpleLabel
     *            the label to be wrapped, not <code>null</code>.
     */
    public SingletonLabelFactory(T simpleLabel) {
        assert simpleLabel != null;
        this.simpleLabel = simpleLabel;
    }

    /**
     * {@inheritDoc}
     * 
     * <p>This factory implementation returns the name of the stored label. 
     */
    @Override 
    public Name name() {
        return simpleLabel.name();
    }

    /**
     * {@inheritDoc}
     * 
     * <p>This implementation does not accept arguments and returns the stored label
     */
    @Override 
    public T parseInstance(List<String> arguments) throws TermLabelException {
        if (arguments.isEmpty()) {
            return simpleLabel;
        } else {
            throw new TermLabelException("Label " + name() + " does not expect arguments");
        }
    }

    /**
     * {@inheritDoc}
     * 
     * <p>This implementation does not accept arguments and returns the stored label
     */
    @Override 
    public T getInstance(List<?> parameters) throws TermLabelException {
        if (parameters.isEmpty()) {
            return simpleLabel;
        } else {
            throw new TermLabelException("Label " + name() + " does not expect arguments");
        }
    }

}
