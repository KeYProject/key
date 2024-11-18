/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.Term;
import org.key_project.logic.op.sv.OperatorSV;
import org.key_project.util.collection.ImmutableList;

public record Trigger(OperatorSV triggerVar, Term trigger, ImmutableList<Term> avoidConditions) {
    public Trigger {
        assert triggerVar != null;
        assert trigger != null;
        assert avoidConditions != null;
    }

    public Term getTerm() {
        return trigger;
    }

    public boolean hasAvoidConditions() {
        return !avoidConditions.isEmpty();
    }
}
