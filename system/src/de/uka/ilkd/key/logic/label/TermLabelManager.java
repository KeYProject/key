package de.uka.ilkd.key.logic.label;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.label.CompositeTermLabelInstantiator;
import de.uka.ilkd.key.rule.label.TermLabelInstantiator;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * This class provides access to the functionality of term labels.
 * 
 * <p>
 * A {@link TermLabelManager} is associated to a {@link Profile} object using
 * {@link Profile#getTermLabelManager()}. It grants access to
 * <ul>
 * <li>The list of names of all registered term labels using
 * {@link #getSupportedLabelNames()}
 * <li>The global {@link TermLabelInstantiator} which is not associated to a
 * particular label.
 * <li>The term label repository using the string parsing function
 * {@link #parseLabel(String, List)}
 * <li>The term label repository using retrieval queries
 * {@link #getLabel(Name, List)} and {@link #getLabel(Name, Object...)}
 * </ul>
 * 
 * <p>
 * Instantiators are usually associated to term labels directly. The methods
 * {@link TermLabel#getInstantiator()} can be used to retrieve the associated
 * instantiator for a label. However, some instantiators do not belong to a
 * label but are <em>global</em>. They are always applied not only on matching
 * terms.
 * 
 * <p>
 * The term label manager is initialised by static methods in the class
 * {@link TermLabels}. They register {@link TermLabelFactory} instances and
 * global {@link TermLabelInstantiator} objects using
 * <ul>
 * <li>{@link #addFactory(TermLabelFactory)}
 * <li>{@link #addGlobalInstantiator(TermLabelInstantiator)}
 * </ul>
 * 
 * <p>
 * Please see information in {@link TermLabels} on how to introduce new label types.
 * </p>
 * 
 * @see TermLabel
 * @see TermLabels
 * @see TermLabelInstantiator
 * 
 * @author Mattias Ulbrich
 */
public class TermLabelManager {

    /**
     * The map from label names to their factories. 
     */
    private final Map<Name, TermLabelFactory<?>> factoryMap = 
            new LinkedHashMap<Name, TermLabelFactory<?>>();
    
    /**
     * The global instantiator.
     * 
     * It is a {@link CompositeTermLabelInstantiator} to accomodate more than one
     * {@link TermLabelInstantiator}. Initially it is null. If this feature is not
     * used, this remains <code>null</code> to make the system more efficient. 
     */
    private CompositeTermLabelInstantiator globalWorker = null;

    /**
     * Get a term label for string parameters.
     * 
     * Parses the string arguments and returns the term label of name
     * <code>name</code> with the corresponding parameters.
     * 
     * <p>
     * The name must be associated with a {@link TermLabelFactory}. Otherwise a
     * {@link TermLabelException} is thrown to indicate that an unknown term
     * label kind has been asked for.
     * 
     * @param name
     *            the name of the term label, not <code>null</code>
     * @param args
     *            the arguments, not <code>null</code>, no entry
     *            <code>null</code>
     * @return term label of kind {@code name} with parameters as parsed.
     * @throws TermLabelException
     *             if name is not a registered label name or the arguments
     *             cannot be parsed.
     */
    public TermLabel parseLabel(String name, List<String> args) throws TermLabelException{

        TermLabelFactory<?> factory = factoryMap.get(new Name(name));
        if(factory == null) {
            throw new TermLabelException("Unknown label name: " + name);
        }

        return factory.parseInstance(args);
    }

    /**
     * Get a term label for object parameters.
     * 
     * Uses the arguments and returns the term label of name
     * <code>name</code> with the parameters.
     * 
     * <p>
     * The name must be associated with a {@link TermLabelFactory}. Otherwise a
     * {@link TermLabelException} is thrown to indicate that an unknown term
     * label kind has been asked for.
     * 
     * @param name
     *            the name of the term label, not <code>null</code>
     * @param args
     *            the arguments, no entry <code>null</code>
     * @return term label of kind {@code name} with parameters.
     * @throws TermLabelException
     *             if name is not a registered label name or the arguments
     *             do not suit the label kind.
     */
    public TermLabel getLabel(Name name, Object... args) throws TermLabelException {
        return getLabel(name, Arrays.asList(args));
    }

    /**
     * Get a term label for object parameters.
     * 
     * Uses the arguments and returns the term label of name
     * <code>name</code> with the parameters.
     * 
     * <p>
     * The name must be associated with a {@link TermLabelFactory}. Otherwise a
     * {@link TermLabelException} is thrown to indicate that an unknown term
     * label kind has been asked for.
     * 
     * @param name
     *            the name of the term label, not <code>null</code>
     * @param args
     *            the arguments, not <code>null</code>, no entry <code>null</code>
     * @return term label of kind {@code name} with parameters.
     * @throws TermLabelException
     *             if name is not a registered label name or the arguments
     *             do not suit the label kind.
     */
    public TermLabel getLabel(Name name, List<?> args) throws TermLabelException {

        TermLabelFactory<?> factory = factoryMap.get(name);
        if(factory == null) {
            throw new TermLabelException("Unknown label name: " + name);
        }

        return factory.getInstance(args);
    }

    /**
     * Adds a term label factory to the lookup table of this manager.
     * 
     * @param factory
     *            the factory to add, not <code>null</code>
     */
    void addFactory(TermLabelFactory<?> factory) {
        assert factory != null;

        Name name = factory.name();
        if(factoryMap.containsKey(name)) {
            // TODO throw exception??
            System.out.println("Label name already registered: " + name);
        }

        factoryMap.put(name, factory);
    }

    /**
     * Returns the global {@link TermLabelInstantiator}.
     * 
     * It is used in all cases when a rule on a {@link Proof} is applied.
     * 
     * @return The {@link TermLabelInstantiator}s to use when a rule is applied.
     */
    public TermLabelInstantiator getGlobalInstantiator() {
        return globalWorker;
    }

    /**
     * Adds a term label instantiator to the list of global instantiators.
     * 
     * @param worker
     *            the instantiator to add.
     */
    void addGlobalInstantiator(TermLabelInstantiator worker) {
        if(globalWorker == null) {
            globalWorker = new CompositeTermLabelInstantiator();
        }
        this.globalWorker.getInstantiatorList().add(worker);
    }
    
    /**
     * Gets the registered supported label names.
     * 
     * @return an unmodifiable collection of names
     */
    public Collection<Name> getSupportedLabelNames() {
        return factoryMap.keySet();
    }

}
