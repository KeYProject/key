// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.proof.examples;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.*;

/** The {@link #run} method of this class will construct a proof object
 * for the sequent that has the formula <code>true</code> in the succedent.  
 * It then prints out the proof and its list of open goals.
 */

public class BuildProofForTrue {

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

    
    /** Return the formula <code>true</code> */
    public Term buildFormula() {
	TermFactory tf = TermFactory.DEFAULT;
	return tf.createJunctorTerm(Op.TRUE, new Term[0]);
    }

    /** return a sequent containing the formula true. */
    public Sequent buildSequent() {
        ConstrainedFormula cf = new ConstrainedFormula(buildFormula());
	Semisequent succ = Semisequent.EMPTY_SEMISEQUENT
	    .insert(0,cf).semisequent();
	return Sequent.createSuccSequent(succ);
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

    /** Build an initial proof with a formula in it. */
    public void run() {
	Proof proof = buildInitialProof();
	printProof("initial Proof",proof);
    }

    public void printProof(String name,Proof proof) {
	System.out.println(name+":");
	System.out.println(proof);
	System.out.println("Open Goals:");
	System.out.println(proof.openGoals());
	System.out.println();
    }

    public static void main(String[] args) {
	new BuildProofForTrue().run();
    }
}

