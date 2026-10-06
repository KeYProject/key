/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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
