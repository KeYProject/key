/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.TacletApplPart;


/** class builds SuccTaclet objects. */
public class SuccTacletBuilder extends FindTacletBuilder<SuccTaclet> {

    private boolean ignoreTopLevelUpdates = true;

    /**
     * sets the <I>find</I> of the Taclet that is to build to the given term, if the sort of the
     * given term is of Sort.FORMULA otherwise nothing happens.
     *
     * @return this SuccTacletBuilder
     */
    public SuccTacletBuilder setFind(Term findTerm) {
        if (findTerm.sort() == Sort.FORMULA) {
            find = findTerm;
        }
        checkContainsFreeVarSV(findTerm, this.getName(), "find term");
        return this;
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
            new TacletApplPart(ifseq, varsNew, varsNotFreeIn, varsNewDependingOn,
                variableConditions),
            goals, ruleSets, attrs, find, ignoreTopLevelUpdates, prefixBuilder.getPrefixMap(),
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


    public void setIgnoreTopLevelUpdates(boolean ignore) {
        ignoreTopLevelUpdates = ignore;
    }
}
