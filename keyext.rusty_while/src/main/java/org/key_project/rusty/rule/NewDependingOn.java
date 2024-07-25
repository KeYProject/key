/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.rusty.logic.op.sv.FormulaSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.logic.op.sv.SkolemTermSV;
import org.key_project.rusty.logic.op.sv.TermSV;

/**
 * TODO: remove?
 * <br>
 * class containing a pair of SchemaVariables, the first one being a TermSV, the second one a
 * FormulaSV, representing a "c new depending on phi" statement within a varcond of a taclet
 */
public class NewDependingOn {
    private final SchemaVariable first;
    private final SchemaVariable second;

    /**
     * constructs a pair of variables given two SchemaVariables. The first SchemaVariable has to
     * occur bound in the Taclet, while the second one can stand for a an arbitrary term of formula,
     * in order to model a pair of the not-free-in relation of an Taclet.
     */
    public NewDependingOn(SchemaVariable first, SchemaVariable second) {
        if (!((first instanceof SkolemTermSV)
                && (second instanceof FormulaSV || second instanceof TermSV))) {
            throw new RuntimeException(
                "NewDependingOn: First SchemaVariable has to be a SkolemTermSV or FormulaSV, "
                    + "the second one has to be a FormulaSV or a TermSV");
        }
        this.first = first;
        this.second = second;
    }

    /**
     * returns the first SchemaVariable of the pair. This SchemaVariable has to be matched to a
     * QuantifiableVariable
     */
    public SchemaVariable first() {
        return first;
    }

    /** returns the second SchemaVariable of the pair. */
    public SchemaVariable second() {
        return second;
    }

    public String toString() {
        return "\\newDependingOn(" + first() + ", " + second() + ")";
    }

    public boolean equals(Object o) {
        if (!(o instanceof NewDependingOn nfi)) {
            return false;
        }
        return (nfi.first == first() && nfi.second == second());
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + first().hashCode();
        result = 37 * result + second().hashCode();
        return result;
    }
}
