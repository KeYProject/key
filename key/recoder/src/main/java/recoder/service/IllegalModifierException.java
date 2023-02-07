/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
