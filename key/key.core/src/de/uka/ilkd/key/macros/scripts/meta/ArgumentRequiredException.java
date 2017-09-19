package de.uka.ilkd.key.macros.scripts.meta;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class ArgumentRequiredException extends InjectionException {
    public ArgumentRequiredException(String message, ProofScriptArgument meta) {
        super(message, meta);
    }
}
