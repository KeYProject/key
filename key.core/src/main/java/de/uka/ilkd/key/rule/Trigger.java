/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;

import org.key_project.util.collection.ImmutableList;

/**
 * @param trigger trigger related information
 */
public record Trigger(SchemaVariable triggerVar, Term trigger, ImmutableList<Term> avoidConditions) {

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
