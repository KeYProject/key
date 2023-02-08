package de.uka.ilkd.key.logic.sort;

/**
 * this exception is thrown if a generic sort has been declared with an illegal supersort
 */
public class GenericSupersortException extends Exception {

    /**
     *
     */
    private static final long serialVersionUID = -5897308261866997061L;
    Sort illegalSort;

    public GenericSupersortException(String description, Sort illegalSort) {
        super(description);
        this.illegalSort = illegalSort;
    }

    public Sort getIllegalSort() {
        return illegalSort;
    }

}
