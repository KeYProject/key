package de.uka.ilkd.key.java.abstraction;

/**
 * A program model element representing variables.
 *
 * @author AL
 * @author RN
 */
public interface Variable extends ProgramModelElement {

    /**
     * Checks if this variable is final.
     *
     * @return <CODE>true</CODE> if this variable is final, <CODE>false</CODE> otherwise.
     */
    boolean isFinal();

    /**
     * Returns the type of this variable.
     *
     * @return the type of this variable.
     */
    Type getType();
}
