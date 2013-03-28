package de.uka.ilkd.key.logic;

public class UnknownLabelException extends RuntimeException {

    /**
     * Generated UID.
     */
    private static final long serialVersionUID = 5930643544197839914L;

    public UnknownLabelException(String labelName) {
        super("Label of type " + labelName + " is unknown.");
    }
    
}
