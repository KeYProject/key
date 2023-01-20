package de.uka.ilkd.key.proof.init;

import org.antlr.runtime.RecognitionException;

/**
 * Reading prover input failed
 */
public class ProofInputException extends RecognitionException {
    private static final long serialVersionUID = 1028674319098864943L;
    private final String message;

    public ProofInputException(Exception e) {
        this(e.getMessage(), e);
    }

    public ProofInputException(String s) {
        this(s, null);
    }

    public ProofInputException(String message, Throwable cause) {
        this.message = message;
        if (cause != null) {
            initCause(cause);
        }
    }

    @Override
    public String getMessage() {
        return message;
    }

}
