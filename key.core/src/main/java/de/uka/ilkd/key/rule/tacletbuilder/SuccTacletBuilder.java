/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.SuccTaclet;

import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;


/** class builds SuccTaclet objects. */
public class SuccTacletBuilder extends FindTacletBuilder<SuccTaclet> {
    /**
     * sets the <I>find</I> of the Taclet that is to build to the given sequent.
     *
     * @return this SuccTacletBuilder
     */
    public SuccTacletBuilder setFind(Sequent findSeq) {
        find = findSeq;
        checkContainsFreeVarSV(findSeq, this.getName(), "find sequent");
        return this;
    }

    /**
     * sets the <I>find</I> of the Taclet that is to build to the sequent {@code ==> findTerm}.
     *
     * @return this SuccTacletBuilder
     */
    public SuccTacletBuilder setFind(JTerm findTerm) {
        return setFind(
            JavaDLSequentKit.createSuccSequent(ImmutableList.of(new SequentFormula(findTerm))));
    }

    /**
     * adds a new goal descriptions to the goal descriptions of the Taclet. the TacletGoalTemplate
     * must not be an RewriteTacletGoalTemplate, otherwise an illegal argument exception is thrown.
     */
    public void addTacletGoalTemplate(TacletGoalTemplate goal) {
        if (goal instanceof RewriteTacletGoalTemplate) {
            throw new TacletBuilderException(this,
                "Tried to add a RewriteTaclet" + "GoalTemplate to a Succ" + "Taclet");
        }
        goals = goals.prepend(goal);
    }


    /**
     * builds and returns the SuccTaclet that is specified by former set... / add... methods. If no
     * name is specified then an Taclet with an empty string name is build. No specifications for
     * variable conditions, goals or heuristics imply that the corresponding parts of the Taclet are
     * empty. No specification for the if-sequence is represented as a sequent with two empty
     * semisequents. No specification for the interactive or recursive flags imply that the flags
     * are not set. No specified find part causes an IllegalStateException. Throws an
     * TacletBuilderException if a bound SchemaVariable occurs more than once in if and find or an
     * InvalidPrefixException if the building of the Taclet Prefix fails.
     */
    public SuccTaclet getSuccTaclet() {
        if (find == null) {
            throw new TacletBuilderException(this, "No find part specified");

        }
        checkBoundInIfAndFind();
        final TacletPrefixBuilder prefixBuilder = new TacletPrefixBuilder(this);
        prefixBuilder.build();
        SuccTaclet t = new SuccTaclet(name,
            new TacletApplPart(ifseq,
                applicationRestriction.combine(ApplicationRestriction.SUCCEDENT_POLARITY), varsNew,
                varsNotFreeIn, varsNewDependingOn,
                variableConditions),
            goals, ruleSets, attrs, (Sequent) find,
            prefixBuilder.getPrefixMap(),
            choices, tacletAnnotations);
        t.setOrigin(origin);
        return t;
    }

    /**
     * builds and returns the Taclet that is specified by former set... / add... methods. If no name
     * is specified then an Taclet with an empty string name is build. No specifications for
     * variable conditions, goals or heuristics imply that the corresponding parts of the Taclet are
     * empty. No specification for the if-sequence is represented as a sequent with two empty
     * semisequences. No specification for the interactive or recursive flags imply that the flags
     * are not set. No specified find part causes an IllegalStateException.
     */
    public SuccTaclet getTaclet() {
        return getSuccTaclet();
    }
}
