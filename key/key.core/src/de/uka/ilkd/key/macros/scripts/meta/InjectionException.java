package de.uka.ilkd.key.macros.scripts.meta;

/**
 *
 *
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class InjectionException extends Exception{

    private static final long serialVersionUID = 4922701573932568352L;
    private final ProofScriptArgument<?> argument;

    public InjectionException(String message, ProofScriptArgument<?> argument) {
        super(message);
        this.argument = argument;
    }

    public InjectionException(String message, Throwable cause, ProofScriptArgument<?> argument) {
        super(message, cause);
        this.argument = argument;
    }

    /**
     *
     * @return
     */
    public ProofScriptArgument<?> getArgument() {
        return argument;
    }
}
