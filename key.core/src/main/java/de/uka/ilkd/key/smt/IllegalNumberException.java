/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;


public class IllegalNumberException extends RuntimeException {

    private static final long serialVersionUID = 1L;

    IllegalNumberException(String msg) {
        super(msg);
    }

}
