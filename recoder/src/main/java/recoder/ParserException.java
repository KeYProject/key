/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

/**
 * Parser exception.
 *
 * @author <TT>AutoDoc</TT>
 */
public class ParserException extends Exception {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7809348545251950515L;

    /**
     * Parser exception.
     */
    public ParserException() {
        super();
    }

    /**
     * Parser exception.
     *
     * @param msg a string.
     */
    public ParserException(String msg) {
        super(msg);
    }
}
