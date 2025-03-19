/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.Sequent;

import org.key_project.util.collection.ImmutableList;

/**
 * container for the application part of an Taclet. It contains an if-sequence, a list of new
 * variables and a list of variable pairs inidcating the NotFreeIn relation and a list of program
 * variables to be added to the program context.
 */
public class TacletApplPart {

    private final Sequent ifseq;
    private final ImmutableList<NewVarcond> varsNew;
    private final ImmutableList<NotFreeIn> varsNotFreeIn;
    private final ImmutableList<NewDependingOn> varsNewDependingOn;
    private final ImmutableList<VariableCondition> variableConditions;

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
