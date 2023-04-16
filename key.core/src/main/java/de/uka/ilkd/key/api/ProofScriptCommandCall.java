package de.uka.ilkd.key.api;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

/**
 * @param <T>
 * @author Alexander Weigl
 */
public class ProofScriptCommandCall<T> {
    final T parameter;
    final ProofScriptCommand<T> command;

    public ProofScriptCommandCall(ProofScriptCommand<T> command, T arguments) {
        parameter = arguments;
        this.command = command;
    }
}
