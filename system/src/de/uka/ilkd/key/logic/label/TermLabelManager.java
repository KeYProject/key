package de.uka.ilkd.key.logic.label;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermLabel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.label.CompositeTermLabelInstantiator;
import de.uka.ilkd.key.rule.label.TermLabelInstantiator;
import de.uka.ilkd.key.util.LinkedHashMap;

public class TermLabelManager {

    private final Map<Name, TermLabelFactory<?>> factoryMap = 
            new LinkedHashMap<Name, TermLabelFactory<?>>();
    
    private CompositeTermLabelInstantiator globalWorker = null;

    public TermLabel parseLabel(String name, List<String> args) throws TermLabelException{

        TermLabelFactory<?> factory = factoryMap.get(new Name(name));
        if(factory == null) {
            throw new TermLabelException("Unknown label name: " + name);
        }

        return factory.parse(args);
    }

    public TermLabel createLabel(Name name, Object... args) throws TermLabelException {
        return createLabel(name, Arrays.asList(args));
    }

    public TermLabel createLabel(Name name, List<?> args) throws TermLabelException {

        TermLabelFactory<?> factory = factoryMap.get(name);
        if(factory == null) {
            throw new TermLabelException("Unknown label name: " + name);
        }

        return factory.create(args);
    }

    public void addFactory(TermLabelFactory<?> factory) {
        Name name = factory.name();
        if(factoryMap.containsKey(name)) {
            // TODO throw exception?
            System.out.println("Label name already registered: " + name);
        }

        factoryMap.put(name, factory);
    }

    /**
     * <p>
     * Returns the {@link TermLabelInstantiator}s to use when a rule on a {@link Proof} of this {@link Profile} is applied.
     * </p>
     * <p>
     * For more information about {@link TermLabel} read its documentation.
     * </p>
     * @return The {@link TermLabelInstantiator}s to use when a rule is applied.
     * @see TermLabel
     */
    public TermLabelInstantiator getGlobalInstantiator() {
        return globalWorker;
    }

    /**
     * @param worker the worker to set
     */
    public void addGlobalWorker(TermLabelInstantiator worker) {
        if(globalWorker == null) {
            globalWorker = new CompositeTermLabelInstantiator();
        }
        this.globalWorker.getInstantiatorList().add(worker);
    }
    
    public Collection<Name> getSupportedLabelNames() {
        return factoryMap.keySet();
    }

}
