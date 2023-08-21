/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

public class AbbrevException extends Exception {

    /**
     *
     */
    private static final long serialVersionUID = 7602628448672131434L;
    protected final boolean termused;

    public AbbrevException(String message, boolean termused) {
        super(message);
        this.termused = termused;
    }
}
