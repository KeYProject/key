/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;


public abstract class SVInstantiationException extends Exception {

    /**
     *
     */
    private static final long serialVersionUID = 7716370813981234134L;
    private final String description;

    public SVInstantiationException(String description) {
        super("Instantiation Error");
        this.description = description;
    }

    public String getMessage() {
        return description;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }
}
