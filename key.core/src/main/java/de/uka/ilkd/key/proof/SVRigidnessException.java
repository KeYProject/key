/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Position;

public class SVRigidnessException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = -440942650851579438L;
    private final String toInstantiate;

    public SVRigidnessException(String toInstantiate, Position position) {
        super("Non-rigid term/formula", position, false);
        this.toInstantiate = toInstantiate;
    }

    public String getMessage() {
        String errmsg = super.getMessage();
        errmsg += "\n " + toInstantiate + " may be instantiated with rigid terms/formulas only";
        return errmsg;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }
}
