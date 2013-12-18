package de.uka.ilkd.key.logic.label;

import java.util.List;

/**
 * A factory for creating TermLabel objects.
 *
 * <p>
 * The method in this factory allow you to retrieve term labels with given
 * parameters. However, a factory may choose to reuse term labels rather than
 * create new objects on every call.
 *
 * <p>
 * Factories are identified by a name. This name corresponds to the name of the
 * {@link TermLabel} objects they create. When parsing all queries to a label
 * will be delegated to the factory with the same name.
 *
 * <p>
 * Please see information in {@link TermLabels} on how to introduce new label
 * types.
 * </p>
 *
 * @param <T>
 *            the type of term labels which are returned by this factory.
 *
 * @see SingletonLabelFactory
 * @author Mattias Ulbrich
 *
 */
public interface TermLabelFactory<T extends TermLabel> {
    /**
     * Parses the arguments and produces a term label.
     *
     * <p>
     * An implementation should throw a {@link TermLabelException} if the
     * arguments cannot be parsed correctly for this type.
     *
     * @param arguments
     *            the arguments for parsing, not <code>null</code>, no entry
     *            <code>null</code>
     *
     * @return the according term label with the given arguments, not
     *         <code>null</code>
     *
     * @throws TermLabelException
     *             if the parameters were illegally formatted
     */
    public T parseInstance(List<String> arguments) throws TermLabelException;
}
