/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.tacletbuilder;

import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.Taclet;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

public class AntecSuccTacletGoalTemplate extends TacletGoalTemplate {
    /** sequent that replaces another one */
    private Sequent replacewith = Sequent.EMPTY_SEQUENT;

    /**
     * creates new Goaldescription
     *
     * @param addedSeq new Sequent to be added
     * @param addedRules IList<Taclet> contains the new allowed rules at this branch
     * @param replacewith the Sequent that replaces another one
     */
    public AntecSuccTacletGoalTemplate(Sequent addedSeq, ImmutableList<Taclet> addedRules,
            Sequent replacewith, ImmutableSet<SchemaVariable> pvs) {
        super(addedSeq, addedRules, pvs);
        // TacletBuilder.checkContainsFreeVarSV(replacewith, null, "replacewith sequent");
        this.replacewith = replacewith;
    }

    public AntecSuccTacletGoalTemplate(Sequent addedSeq, ImmutableList<Taclet> addedRules,
            Sequent replacewith) {
        this(addedSeq, addedRules, replacewith, DefaultImmutableSet.nil());
    }

    /**
     * a Taclet may replace a Sequent by another. The new Sequent is returned. this Sequent.
     *
     * @return Sequent being paramter in the rule goal replacewith(Seq)
     */
    public Sequent replaceWith() {
        return replacewith;
    }
}
