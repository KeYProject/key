// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.proof.examples;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.*;

/** The {@link #run} method of this class will construct a proof object
 * for the empty sequent.  It then prints out the proof and its list of 
 * open goals.
 */

public class BuildEmptyProof {

    /** Return a taclet index with no taclets in it. */
    public TacletIndex buildTacletIndex() {
	return new TacletIndex();
    }

    /** Return an empty built-in rule index */
    public BuiltInRuleIndex buildBuiltInRuleIndex() {
	return new BuiltInRuleIndex();
    }

    /** Return a RuleAppIndex appropriate for our rules.*/
    public RuleAppIndex buildRuleAppIndex() {
	return 
	    new RuleAppIndex(new TacletAppIndex(buildTacletIndex()),
			     new BuiltInRuleAppIndex(buildBuiltInRuleIndex()));
    }

    /** return an empty sequent. */
    public Sequent buildSequent() {
	return Sequent.EMPTY_SEQUENT;
    }

    /** return the proof for the constructed sequent. */
    public Proof buildInitialProof() {
	Proof proof = new Proof(new Services());
	Sequent seq = buildSequent();
	Node rootNode = new Node(proof,seq);
	proof.setRoot(rootNode);
	Goal firstGoal = new Goal(rootNode,buildRuleAppIndex());
	proof.add(firstGoal);
	return proof;
    }

    /** build a Proof object for the empty sequent. */
    public void run() {
	Proof proof = buildInitialProof();

	System.out.println(proof);
	System.out.println("Open Goals:");
	System.out.println(proof.openGoals());
    }

    public static void main(String[] args) {
	new BuildEmptyProof().run();
    }
}

