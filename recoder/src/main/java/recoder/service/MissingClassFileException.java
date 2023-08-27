/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import recoder.ModelException;

/**
 * Exception indicating that a vital class file is missing, usually a super type of a known class
 * file.
 *
 * @author AL
 * @since 0.72
 */
public class MissingClassFileException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 3265837360603622631L;
    private final String missingClass;

    /**
     * Empty constructor.
     *
     * @param name the name of the missing file.
     */
    public MissingClassFileException(String name) {
        this.missingClass = name;
    }

    /**
     * Constructor with an explanation text.
     *
     * @param s an explanation.
     * @param name the name of the missing file.
     */
    public MissingClassFileException(String s, String name) {
        super(s);
        this.missingClass = name;
    }

    /**
     * Returns the program element that could not be resolved.
     */
    public String getMissingClassFileName() {
        return missingClass;
    }
}
