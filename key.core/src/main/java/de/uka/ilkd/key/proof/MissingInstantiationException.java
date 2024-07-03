/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.proof;


public class MissingInstantiationException
        extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = 6424217152885699595L;
    private String toInstantiate;

    public MissingInstantiationException(String toInstantiate,
            int row,
            int column,
            boolean inIfSequent) {
        super("Missing Instantantiation", row, column, inIfSequent);
        this.toInstantiate = toInstantiate;
    }

    public String getMessage() {
        String errmsg = super.getMessage();
        errmsg += "\n Instantiation missing for " + toInstantiate;
        return errmsg;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }
}
