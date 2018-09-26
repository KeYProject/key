package de.uka.ilkd.key.macros.scripts.meta;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class ConversionException extends InjectionException {

    private static final long serialVersionUID = -5720036164543586030L;

    public ConversionException(String message,
                               ProofScriptArgument<?> argument) {
        super(message, argument);
    }

    public ConversionException(String message, Throwable cause,
                               ProofScriptArgument<?> argument) {
        super(message, cause, argument);
    }
}
