/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
