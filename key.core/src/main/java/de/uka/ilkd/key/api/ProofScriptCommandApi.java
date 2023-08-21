/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.ServiceLoader;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

/**
 * This class provides access to the proof script commands.
 *
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public class ProofScriptCommandApi {
    private final Map<String, ProofScriptCommand> commandMap = new HashMap<>();

    public ProofScriptCommandApi() {
        initialize();
    }

    private void initialize() {
        ServiceLoader<ProofScriptCommand> loader = ServiceLoader.load(ProofScriptCommand.class);
        loader.forEach(psc -> commandMap.put(psc.getName(), psc));
    }

    /**
     * Returns a collection of all registered proof script commands.
     * <p>
     * {@link ProofScriptCommand}s are found via the {@link ServiceLoader} facility.
     *
     * @return a collection of proof script commands
     */
    public Collection<ProofScriptCommand> getScriptCommands() {
        return commandMap.values();
    }

    /**
     * Searches for the proof script command in the registered commands by its name. If no command
     * is found, null is returned.
     *
     * @param name the non-null name of the search proof script command
     * @return the proof script command or null
     */
    public ProofScriptCommand<?> getScriptCommands(String name) {
        return commandMap.get(name);
    }
}
