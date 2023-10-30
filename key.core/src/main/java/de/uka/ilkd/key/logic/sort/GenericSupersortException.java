/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

/**
 * this exception is thrown if a generic sort has been declared with an illegal supersort
 */
public class GenericSupersortException extends Exception {

    /**
     *
     */
    private static final long serialVersionUID = -5897308261866997061L;
    final Sort illegalSort;

    public GenericSupersortException(String description, Sort illegalSort) {
        super(description);
        this.illegalSort = illegalSort;
    }

    public Sort getIllegalSort() {
        return illegalSort;
    }

}
