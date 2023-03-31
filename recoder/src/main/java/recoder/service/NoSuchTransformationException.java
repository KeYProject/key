// This file is part of the RECODER library and protected by the LGPL.

package recoder.service;

import recoder.ModelException;
import recoder.kit.Transformation;

/**
 * Exception indicating that a transformation is not accessible.
 *
 * @author AL.
 */
public class NoSuchTransformationException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1118670095981879663L;

    /**
     * Empty constructor.
     */
    public NoSuchTransformationException() {
        super();
    }

    /**
     * Empty constructor.
     */
    public NoSuchTransformationException(Transformation transformation) {
        this("Transformation not found: " + transformation.toString());
    }

    /**
     * Constructor with an explanation text.
     *
     * @param s an explanation.
     */
    public NoSuchTransformationException(String s) {
        super(s);
    }
}
