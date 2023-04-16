package de.uka.ilkd.key.pp;

public class AbbrevException extends Exception {

    /**
     *
     */
    private static final long serialVersionUID = 7602628448672131434L;
    protected final boolean termused;

    public AbbrevException(String message, boolean termused) {
        super(message);
        this.termused = termused;
    }
}
