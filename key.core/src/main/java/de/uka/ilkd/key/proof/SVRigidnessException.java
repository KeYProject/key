package de.uka.ilkd.key.proof;

public class SVRigidnessException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = -440942650851579438L;
    private String toInstantiate;

    public SVRigidnessException(String toInstantiate, int row, int column) {
        super("Non-rigid term/formula", row, column, false);
        this.toInstantiate = toInstantiate;
    }

    public String getMessage() {
        String errmsg = super.getMessage();
        errmsg += "\n " + toInstantiate + " may be instantiated with rigid terms/formulas only";
        return errmsg;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }
}
