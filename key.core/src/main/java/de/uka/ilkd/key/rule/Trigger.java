/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;

import org.key_project.util.collection.ImmutableList;

public class Trigger {

    /** trigger related information */
    private final Term trigger;
    private final ImmutableList<Term> avoidConditions;
    private final SchemaVariable triggerVar;


    public Trigger(SchemaVariable triggerVar, Term trigger, ImmutableList<Term> avoidConditions) {
        assert triggerVar != null;
        assert trigger != null;
        assert avoidConditions != null;

        this.triggerVar = triggerVar;
        this.trigger = trigger;
        this.avoidConditions = avoidConditions;
    }


    public SchemaVariable getTriggerVar() {
        return triggerVar;
    }

    public Term getTerm() {
        return trigger;
    }

    public ImmutableList<Term> getAvoidConditions() {
        return avoidConditions;
    }

    public boolean hasAvoidConditions() {
        return !avoidConditions.isEmpty();
    }

}
