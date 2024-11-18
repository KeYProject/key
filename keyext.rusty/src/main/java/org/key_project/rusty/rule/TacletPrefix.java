/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;


import org.key_project.rusty.logic.op.sv.SchemaVariable;

/**
 * @param prefixLength  the prefix of the taclet
 * @param context used by rewrite taclets to mark the context
 */
public record TacletPrefix(int prefixLength, boolean context) implements org.key_project.prover.rules.TacletPrefix {
    /**
     * creates the prefix
     *
     * @param prefixLength  the SetOf<SchemaVariable> that is the prefix of a termsv or formulasv
     * @param context a boolean marker
     */
    public TacletPrefix {
    }

    /**
     * returns a new TacletPrefix with the context flag set to the given boolean value
     *
     * @param setTo the boolean to which the TacletPrefix is set to
     * @return a newly created TacletPrefix
     */
    public TacletPrefix setContext(boolean setTo) {
        return new TacletPrefix(prefixLength, setTo);
    }

    /**
     * creates a new TacletPrefix with a new prefix entry
     *
     * @return the new prefix
     */
    public TacletPrefix increase() {
        return new TacletPrefix(prefixLength+1, context);
    }

    /**
     * removes a SchemaVariable from the prefix
     *
     * @param var the SchemaVariable to be removed
     * @return the new prefix
     */
    public TacletPrefix decrease(SchemaVariable var) {
        assert prefixLength > 0;
        return new TacletPrefix(prefixLength-1, context);
    }

    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (!(o instanceof TacletPrefix other)) {
            return false;
        }
        return (other.prefixLength() == prefixLength()) && (other.context() == context());
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + prefixLength();
        result = 37 * result + (context() ? 0 : 1);
        return result;
    }

    public String toString() {
        return "TacletPrefix: " + prefixLength() + (context() ? "+ { K }" : "");
    }
}
