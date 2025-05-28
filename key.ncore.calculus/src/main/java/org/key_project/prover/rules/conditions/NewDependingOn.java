/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.conditions;

import org.key_project.logic.op.sv.SchemaVariable;

///
/// class containing a pair of SchemaVariables, the first one being a TermSV, the second one a
/// FormulaSV, representing a "c new depending on phi" statement within a varcond of a taclet
public record NewDependingOn(SchemaVariable first, SchemaVariable second) {
    /// constructs a pair of variables given two SchemaVariables. The first SchemaVariable has to
    /// occur bound in the Taclet, while the second one can stand for an arbitrary term of formula,
    /// in order to model a pair of the not-free-in relation of a Taclet.
    public NewDependingOn {
        if (!((first.isSkolemTerm()) && (second.isFormula() || second.isTerm()))) {
            throw new RuntimeException(
                "NewDependingOn: First SchemaVariable has to be a SkolemTermSV or FormulaSV, "
                    + "the second one has to be a FormulaSV or a TermSV");
        }
    }

    /// returns the first SchemaVariable of the pair. This SchemaVariable has to be matched to a
    /// QuantifiableVariable
    @Override
    public SchemaVariable first() { return first; }

    /// returns the second SchemaVariable of the pair.
    @Override
    public SchemaVariable second() { return second; }

    public String toString() { return "\\newDependingOn(" + first() + ", " + second() + ")"; }

    public boolean equals(Object o) {
        if (!(o instanceof NewDependingOn(SchemaVariable first1, SchemaVariable second1))) {
            return false;
        }
        return (first1 == first() && second1 == second());
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + first().hashCode();
        result = 37 * result + second().hashCode();
        return result;
    }
}
