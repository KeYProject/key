/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.tacletbuilder;

import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.proof.calculus.RustySequentKit;
import org.key_project.rusty.rule.Taclet;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

public class RewriteTacletGoalTemplate extends TacletGoalTemplate {
    /** term that replaces another one */
    private final Term replacewith;

    /**
     * creates new Goaldescription
     *
     * @param addedSeq new Sequent to be added
     * @param addedRules IList<Taclet> contains the new allowed rules at this branch
     * @param replacewith the Term that replaces another one
     * @param pvs the set of schema variables
     */
    public RewriteTacletGoalTemplate(org.key_project.prover.sequent.Sequent addedSeq,
            ImmutableList<Taclet> addedRules,
            Term replacewith, ImmutableSet<SchemaVariable> pvs) {
        super(addedSeq, addedRules, pvs);
        // TacletBuilder.checkContainsFreeVarSV(replacewith, null, "replacewith term");
        this.replacewith = replacewith;
    }

    public RewriteTacletGoalTemplate(org.key_project.prover.sequent.Sequent addedSeq,
            ImmutableList<Taclet> addedRules,
            Term replacewith) {
        this(addedSeq, addedRules, replacewith, DefaultImmutableSet.nil());
    }


    public RewriteTacletGoalTemplate(Term replacewith) {
        this(RustySequentKit.getInstance().getEmptySequent(), ImmutableSLList.nil(), replacewith);
    }


    /**
     * a Taclet may replace a Term by another. The new Term is returned.
     *
     * @return Term being paramter in the rule goal replacewith(Seq)
     */
    public Term replaceWith() {
        return replacewith;
    }
}
