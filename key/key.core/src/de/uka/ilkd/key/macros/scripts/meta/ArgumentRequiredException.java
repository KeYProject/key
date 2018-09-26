package de.uka.ilkd.key.macros.scripts.meta;

/**
 * Signals if an argument is required but was not set during an injection.
 *
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class ArgumentRequiredException extends InjectionException {

    private static final long serialVersionUID = -5868248545891789842L;

    public ArgumentRequiredException(String message, ProofScriptArgument<?> meta) {
        super(message, meta);
    }
}
