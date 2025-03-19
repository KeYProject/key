/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

/**
 * this exception is thrown if an invalid instantiation for a schema variable was given
 */
public class IllegalInstantiationException extends RuntimeException {

    /**
     *
     */
    private static final long serialVersionUID = -9139512430789901488L;

    public IllegalInstantiationException(String description) {
        super(description);
    }


}
