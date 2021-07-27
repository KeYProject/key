package de.uka.ilkd.key.api;

import de.uka.ilkd.key.macros.ProofMacro;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.ServiceLoader;

/**
 * This class provides access to the proof script commands.
 *
 * @author Alexander Weigl
 * @version 1 (09.05.17)
 */
public class ProofMacroApi {
    private Map<String, ProofMacro> commandMap = new HashMap<>();

    public ProofMacroApi() {
        initialize();
    }

    private void initialize() {
        ServiceLoader<ProofMacro> loader = ServiceLoader.load(ProofMacro.class);
        loader.forEach(psc -> {
            if (psc.getScriptCommandName() != null)
                commandMap.put(psc.getScriptCommandName(), psc);
        });
    }

    /**
     * Returns a collection of all registered proof script commands.
     * <p>
     * {@link ProofMacro}s are found via the {@link ServiceLoader} facility.
     *
     * @return a collection of proof script commands
     */
    public Collection<ProofMacro> getMacros() {
        return commandMap.values();
    }

    /**
     * Searches for the proof script command in the registered commands by its name.
     * If no command is found, null is returned.
     *
     * @param name the non-null name of the search proof script command
     * @return the proof script command or null
     */
    public ProofMacro getMacro(String name) {
        return commandMap.get(name);
    }
}
