package de.uka.ilkd.key.proof;

/** this exception thrown if an if-sequent match failed */
public class IfMismatchException extends SVInstantiationException {

    /**
     *
     */
    private static final long serialVersionUID = 933425921270034135L;

    public IfMismatchException(String description) {
        super(description);
    }


}
