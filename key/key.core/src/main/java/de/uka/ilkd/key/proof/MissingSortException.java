package de.uka.ilkd.key.proof;


public class MissingSortException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = 2491948230461429971L;
    private String toInstantiate;

    public MissingSortException(String toInstantiate, int row, int column) {
        super("Missing Sort", row, column, false);
        this.toInstantiate = toInstantiate;
    }

    public String getMessage() {
        String errmsg = super.getMessage();
        errmsg += "\n Sort of " + toInstantiate + " is unknown.\n"
            + "The sort can be given manually using an expression like \"id:sort\".";
        return errmsg;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }
}
