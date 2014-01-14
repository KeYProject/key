package de.uka.ilkd.key.logic.label;

/**
 * An exception which can be thrown by the term label system.
 *
 * <p>
 * {@link TermLabelFactory} methods can throw an instance if the requested term
 * label cannot be created.
 *
 * <p>
 * {@link TermLabelManager} can throw this if a requested label name has not
 * been registered.
 *
 * @author mattias ulbrich
 */

@SuppressWarnings("serial")
public class TermLabelException extends Exception {

    public TermLabelException() {
        super();
    }

    public TermLabelException(String message, Throwable cause) {
        super(message, cause);
    }

    public TermLabelException(String message) {
        super(message);
    }

    public TermLabelException(Throwable cause) {
        super(cause);
    }

}
