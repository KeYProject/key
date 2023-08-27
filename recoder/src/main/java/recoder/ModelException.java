/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

/**
 * Model exception.
 *
 * @author <TT>AutoDoc</TT>
 */
public class ModelException extends RuntimeException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -2334025270847777367L;

    /**
     * Model exception.
     */
    public ModelException() {
        super();
    }

    /**
     * Model exception.
     *
     * @param s a string.
     */
    public ModelException(String s) {
        super(s);
    }
}
