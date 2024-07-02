// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;

/** an object indicating that a proof event has happpend */
public class ProofEvent {

    /**
     * the proof where an event happened
     */
    private final Proof source;

    /**
     * if the proof event is the result of rule applications the following to fields
     * have a non-null value, otherwise null
     */
    private RuleAppInfo ruleAppInfo = null;
    
    /**
     * new goals created by an applied rule; empty if goal was closed and null if this event
     * does not relate to a rule application
     */
    private ImmutableList<Goal> newGoals = null;

    /**
     * creates a new proof event the interactive prover where the event initially
     * occured
     *
     * @param source the source event
     */
    public ProofEvent(Proof source) {
        this.source = source;
    }

    /**
     * creates a proof event for a change triggered by a rule applications
     * @param source the Proof where the rule was applied
     * @param rai the RuleAppInfo object with further information about the changes
     * @param newGoals the list of newly created goals (empty in case a goal was closed)
     */
    public ProofEvent(Proof source, RuleAppInfo rai, ImmutableList<Goal> newGoals) {
        this(source);
        ruleAppInfo = rai;
        this.newGoals = newGoals;
    }

    /**
     * the proof from where this even to originated
     * @return the proof
     */
    public Proof getSource() {
        return source;
    }

    /**
     * This information should have its own event, but is currently propagated via
     * this one
     * @return information object about the effects of the applied rule
     */
    public RuleAppInfo getRuleAppInfo() {
        return ruleAppInfo;
    }

    /**
     * returns the list of new goals (empty if a goal was closed) in case of a rule
     * application otherwise null
     *
     * @return the list of new goals (empty if a goal was closed) in case of a rule
     *         application otherwise null
     */
    public ImmutableList<Goal> getNewGoals() {
        return newGoals;
    }
}