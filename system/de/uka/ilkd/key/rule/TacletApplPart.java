// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/**
 * container for the application part of an Taclet. It contains an
 * if-sequence, a list of new variables and a list of variable pairs
 * inidcating the NotFreeIn relation and a list of program variables to
 * be added to the program context.
 */

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.Sequent;

public class TacletApplPart {

    private Sequent ifseq;
    private ListOfNewVarcond varsNew;
    private ListOfNotFreeIn varsNotFreeIn;
    private ListOfNewDependingOn varsNewDependingOn;
    private ListOfVariableCondition variableConditions;

    /** constructs a new TacletApplPart object with the given Sequent,
     * a list of variables that are new, a list of variable pairs that
     * represent the NotFreeIn relation and a list of additional
     * generic variable conditions.
     */
    public TacletApplPart(Sequent              ifseq,
			  ListOfNewVarcond     varsNew,
			  ListOfNotFreeIn      varsNotFreeIn,
			  ListOfNewDependingOn varsNewDependingOn,
			  ListOfVariableCondition variableConditions) {
	this.ifseq=ifseq;
	this.varsNew=varsNew;
	this.varsNotFreeIn=varsNotFreeIn;
	this.varsNewDependingOn=varsNewDependingOn;
	this.variableConditions = variableConditions;
    }

    /** returns the if-sequent of the application part of a Taclet */
    public Sequent ifSequent() {
	return ifseq;
    } 

    /** returns the list of variables that are new in a Taclet */
    public ListOfNewVarcond varsNew() {
	return varsNew;
    } 

    /** returns the list of variable pairs that represent the
     * NotFreeIn relation of a Taclet
     */
    public ListOfNotFreeIn varsNotFreeIn() {
	return varsNotFreeIn;
    } 

    /** returns the list of variable pairs that represent the
     * "new depending on" relation of a Taclet
     */
    public ListOfNewDependingOn varsNewDependingOn() {
	return varsNewDependingOn;
    } 

    /** returns the list of additional generic conditions on
     * instantiations of schema variables. The list ist readonly. */
    public ListOfVariableCondition getVariableConditions() {
	return variableConditions;
    }

}
