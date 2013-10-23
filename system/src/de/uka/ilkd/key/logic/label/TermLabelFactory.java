package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.TermLabel;

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
 * Please see information in {@link TermLabelUtil} on how to introduce new label
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
interface TermLabelFactory<T extends TermLabel> extends Named {

     /**
     * Returns the name of this term label factory.
     * 
     * Use the same name for term labels and their factories.
     * 
     * @return the name of the factory, not <code>null</code>
     */
    @Override
    public Name name();

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

    /**
     * Returns the term label for the given parameters.
     * 
     * <p>
     * An implementation should throw a {@link TermLabelException} if the
     * arguments are not suitable for this type.
     * 
     * @param parameters
     *            the parameters for the term label 
     *
     * @return the according term label with the given arguments, not <code>null</code>
     * 
     * @throws TermLabelException
     *             if the parameters were illegal
     */
    public T getInstance(List<?> parameters) throws TermLabelException;

}
