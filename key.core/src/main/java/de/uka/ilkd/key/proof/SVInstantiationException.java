package de.uka.ilkd.key.proof;


public abstract class SVInstantiationException extends Exception {

    /**
     *
     */
    private static final long serialVersionUID = 7716370813981234134L;
    private final String description;

    public SVInstantiationException(String description) {
        super("Instantiation Error");
        this.description = description;
    }

    public String getMessage() {
        return description;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }
}
