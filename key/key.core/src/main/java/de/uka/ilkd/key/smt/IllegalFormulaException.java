/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.smt;

public class IllegalFormulaException extends Exception {
    /**
     *
     */
    private static final long serialVersionUID = 1L;

    IllegalFormulaException(String msg) {
        super(msg);
    }
}
