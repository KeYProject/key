package de.uka.ilkd.key.macros.scripts.meta;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class InjectionReflectionException extends InjectionException {
    public InjectionReflectionException(String message, ProofScriptArgument argument) {
        super(message, argument);
    }

    public InjectionReflectionException(String message, Throwable cause, ProofScriptArgument argument) {
        super(message, cause, argument);
    }
}
