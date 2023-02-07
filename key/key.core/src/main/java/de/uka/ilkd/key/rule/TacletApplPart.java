/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.rule;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Sequent;

public class TacletApplPart {

    private Sequent ifseq;
    private ImmutableList<NewVarcond> varsNew;
    private ImmutableList<NotFreeIn> varsNotFreeIn;
    private ImmutableList<NewDependingOn> varsNewDependingOn;
    private ImmutableList<VariableCondition> variableConditions;

    /**
     * constructs a new TacletApplPart object with the given Sequent, a list of variables that are
     * new, a list of variable pairs that represent the NotFreeIn relation and a list of additional
     * generic variable conditions.
     */
    public TacletApplPart(Sequent ifseq, ImmutableList<NewVarcond> varsNew,
            ImmutableList<NotFreeIn> varsNotFreeIn,
            ImmutableList<NewDependingOn> varsNewDependingOn,
            ImmutableList<VariableCondition> variableConditions) {
        this.ifseq = ifseq;
        this.varsNew = varsNew;
        this.varsNotFreeIn = varsNotFreeIn;
        this.varsNewDependingOn = varsNewDependingOn;
        this.variableConditions = variableConditions;
    }

    /** returns the if-sequent of the application part of a Taclet */
    public Sequent ifSequent() {
        return ifseq;
    }

    /** returns the list of variables that are new in a Taclet */
    public ImmutableList<NewVarcond> varsNew() {
        return varsNew;
    }

    /**
     * returns the list of variable pairs that represent the NotFreeIn relation of a Taclet
     */
    public ImmutableList<NotFreeIn> varsNotFreeIn() {
        return varsNotFreeIn;
    }

    /**
     * returns the list of variable pairs that represent the "new depending on" relation of a Taclet
     */
    public ImmutableList<NewDependingOn> varsNewDependingOn() {
        return varsNewDependingOn;
    }

    /**
     * returns the list of additional generic conditions on instantiations of schema variables. The
     * list ist readonly.
     */
    public ImmutableList<VariableCondition> getVariableConditions() {
        return variableConditions;
    }

}
