package de.uka.ilkd.key.macros.scripts;

import java.net.URL;

/**
 * Thrown if during the execution of a command, the proof is already closed. May or may not lead to
 * exceptional termination of the whole script based on the <code>@failonclosed</code> setting.
 *
 * @author Dominic Steinhoefel
 */
public class ProofAlreadyClosedException extends ScriptException {
    private static final long serialVersionUID = 1L;

    public ProofAlreadyClosedException() {
        super();
    }

    public ProofAlreadyClosedException(String message, URL url, int line, int col,
            Throwable cause) {
        super(message, url, line, col, cause);
    }

    public ProofAlreadyClosedException(String message, URL url, int line, int col) {
        super(message, url, line, col);
    }

    public ProofAlreadyClosedException(String message) {
        super(message);
    }

    public ProofAlreadyClosedException(Throwable cause) {
        super(cause);
    }

    public ProofAlreadyClosedException(String message, Throwable cause) {
        super(message, cause);
    }
}
