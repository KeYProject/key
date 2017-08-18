package de.uka.ilkd.key.macros.scripts.meta;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class NoSpecifiedConverterException extends InjectionException {
    public NoSpecifiedConverterException(String message, ProofScriptArgument argument) {
        super(message, argument);
    }

    public NoSpecifiedConverterException(String message, Throwable cause,
                                         ProofScriptArgument argument) {
        super(message, cause, argument);
    }
}
