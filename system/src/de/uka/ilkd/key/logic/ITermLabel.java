package de.uka.ilkd.key.logic;

/**
 * The interface for term labels. Term labels are annotations that can be attached
 * to terms and carry additional information. They must not be soundness relevant.
 */
public interface ITermLabel {

    /**
     * a term label may have structure, i.e., parameterized
     * @param i the i-th parameter (from 0 to max nr of parameters)
     * @return the selected parameter
     * @throw an {@link IndexOutOfBoundsException} if the given parameter number is negative or greater-or-equal the number of parameters returned by {@link #getChildCount()}
     */
    public abstract Object getChild(int i);

    /**
     * number of parameters (non-negative number)
     * @return the number of paramters
     */
    public abstract int getChildCount();

}
