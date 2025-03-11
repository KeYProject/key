/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;


import de.uka.ilkd.key.java.Position;

public class MissingSortException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = 2491948230461429971L;
    private final String toInstantiate;

    public MissingSortException(String toInstantiate, Position position) {
        super("Missing Sort", position, false);
        this.toInstantiate = toInstantiate;
    }

    @Override
    public String getMessage() {
        String errmsg = super.getMessage();
        errmsg += "\n Sort of " + toInstantiate + " is unknown.\n"
            + "The sort can be given manually using an expression like \"id:sort\".";
        return errmsg;
    }

    /**
     * Returns a string representation of this exception.
     */
    @Override
    public String toString() {
        return getMessage();
    }
}
