// This file is part of the RECODER library and protected by the LGPL.

package recoder.service;

import recoder.ModelException;
import recoder.java.ProgramElement;

/**
 * Exception indicating that a particular reference (or reference prefix) could not be resolved.
 *
 * @author AL.
 */
public class UnresolvedReferenceException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 4926742139318960014L;
    private final ProgramElement programElement;

    /**
     * Empty constructor.
     *
     * @param r the program element that could not be resolved.
     */
    public UnresolvedReferenceException(ProgramElement r) {
        programElement = r;
    }

    /**
     * Constructor with an explanation text.
     *
     * @param s an explanation.
     * @param r the program element that could not be resolved.
     */
    public UnresolvedReferenceException(String s, ProgramElement r) {
        super(s);
        programElement = r;
    }

    /**
     * Returns the program element that could not be resolved.
     */
    public ProgramElement getUnresolvedReference() {
        return programElement;
    }
}
