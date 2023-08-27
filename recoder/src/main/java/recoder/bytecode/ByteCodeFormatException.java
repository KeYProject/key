/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import recoder.ParserException;

/**
 * Byte Code format Exception.
 *
 * @author AL
 */
public class ByteCodeFormatException extends ParserException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -6748189319137209773L;

    /**
     * Trivial Constructor.
     */
    public ByteCodeFormatException() {
        super();
    }

    /**
     * Constructor with description text.
     *
     * @param msg a description.
     */
    public ByteCodeFormatException(String msg) {
        super(msg);
    }
}
