package de.uka.ilkd.key.proof;


import de.uka.ilkd.key.java.Position;

public class MissingInstantiationException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = 6424217152885699595L;
    private final String toInstantiate;

    public MissingInstantiationException(String toInstantiate, Position position,
            boolean inIfSequent) {
        super("Missing Instantantiation", position, inIfSequent);
        this.toInstantiate = toInstantiate;
    }

    @Override
    public String getMessage() {
        String errmsg = super.getMessage();
        errmsg += "\n Instantiation missing for " + toInstantiate;
        return errmsg;
    }

    /**
     * Returns a string representation of this exception.
     */
    @Override
    public String toString() {
        return getMessage();
    }
}
