/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

/**
 * @author niederma
 *
 */
public class IllegalResultException extends RuntimeException {


    private static final long serialVersionUID = 1L;

    IllegalResultException(String msg) {
        super(msg);
    }
}
