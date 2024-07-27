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
    private Sequent replaceWith = Sequent.EMPTY_SEQUENT;

    /**
     * creates new GoalDescription
     *
     * @param addedSeq new Sequent to be added
     * @param addedRules IList<Taclet> contains the new allowed rules at this branch
     * @param replaceWith the Sequent that replaces another one
     */
    public AntecSuccTacletGoalTemplate(Sequent addedSeq, ImmutableList<Taclet> addedRules,
            Sequent replaceWith, ImmutableSet<SchemaVariable> pvs) {
        super(addedSeq, addedRules, pvs);
        // TacletBuilder.checkContainsFreeVarSV(replaceWith, null, "replaceWith sequent");
        this.replaceWith = replaceWith;
    }

    public AntecSuccTacletGoalTemplate(Sequent addedSeq, ImmutableList<Taclet> addedRules,
            Sequent replaceWith) {
        this(addedSeq, addedRules, replaceWith, DefaultImmutableSet.nil());
    }

    /**
     * a Taclet may replace a Sequent by another. The new Sequent is returned. this Sequent.
     *
     * @return Sequent being parameter in the rule goal replaceWith(Seq)
     */
    public Sequent replaceWith() {
        return replaceWith;
    }

    /** toString */
    @Override
    public String toString() {
        String result = super.toString();
        result += "\\replacewith(" + replaceWith() + ") ";
        return result;
    }
}
