/*
 * Created on 02.10.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 *
 */
package recoder.service;

import recoder.ModelException;

/**
 * @author Tobias Gutzmann
 */
public class IllegalModifierException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -2930910039583684560L;

    /**
     *
     */
    public IllegalModifierException() {
        super();
    }

    /**
     * @param s
     */
    public IllegalModifierException(String s) {
        super(s);
    }

}
