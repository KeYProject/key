package de.uka.ilkd.key.macros.scripts.meta;

/**
 * Signals if an argument is given that is not part of the defined arguments
 * class.
 *
 * @author Mattias Ulbrich
 */
public class UnknownArgumentException extends InjectionException {

    /**
     * An argument required exception with no cause (to display).
     *
     * @param message the respective String message to be passed.
     */
    public UnknownArgumentException(String message) {
        super(message, null);
    }
}
