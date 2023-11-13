/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.Objects;

import org.key_project.util.EqualsModProofIrrelevancy;


/**
 * All symbols acting as members of a term e.g. logical operators, predicates, functions, variables
 * etc. have to implement this interface.
 */
public interface Operator
        extends org.key_project.logic.op.Operator, SVSubstitute, EqualsModProofIrrelevancy {

    @Override
    default boolean equalsModProofIrrelevancy(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof Operator that)) {
            return false;
        }
        // assume name and arity uniquely identifies operator
        return arity() == that.arity() && name().equals(that.name());
    }

    @Override
    default int hashCodeModProofIrrelevancy() {
        return Objects.hash(arity(), name());
    }
}
