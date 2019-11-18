package de.uka.ilkd.key.pp;

/**
 * This exception is thrown when a String is expected be a valid
 * regular expression, but is not.
 *
 * @author jschiffl
 */
public class IllegalRegexException extends Exception {

    private static final long serialVersionUID = 1113541L;

    /**
     * constructor
     * @param cause the cause of the exception
     */
    public IllegalRegexException(Throwable cause) {
        super(cause);
    }
}