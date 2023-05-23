package de.uka.ilkd.key.proof.init;

/**
 * Reading prover input failed
 */
public class ProofInputException extends Exception {
    private static final long serialVersionUID = 1028674319098864943L;

    public ProofInputException(Throwable e) {
        super(e);
    }

    public ProofInputException(String s) {
        super(s);
    }

    public ProofInputException(String message, Throwable cause) {
        super(message, cause);
    }
}
