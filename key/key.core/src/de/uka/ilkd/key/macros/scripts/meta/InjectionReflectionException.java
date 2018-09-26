package de.uka.ilkd.key.macros.scripts.meta;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class InjectionReflectionException extends InjectionException {

    private static final long serialVersionUID = -5062920998506967420L;

    public InjectionReflectionException(String message,
                                        ProofScriptArgument<?> argument) {
        super(message, argument);
    }

    public InjectionReflectionException(String message, Throwable cause,
                                        ProofScriptArgument<?> argument) {
        super(message, cause, argument);
    }
}
