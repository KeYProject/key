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



import java.util.Iterator;

import junit.framework.TestCase;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.TacletForTests;

/** class tests the tree of proof
*/


public class TestProofTree extends TestCase {
    Proof p;
    Node n1;
    Node n2;
    Node n3;
    Node n4;
    Node n5;
    Node n6;
    Node n7;


    public TestProofTree(String name) {
	super(name);
    }

    public void setUp() {
	Sort s = new SortImpl(new Name("s"));
	LogicVariable b1=new LogicVariable(new Name("b1"),s);
	LogicVariable b2=new LogicVariable(new Name("b2"),s);
	LogicVariable b3=new LogicVariable(new Name("b3"),s);
	LogicVariable b4=new LogicVariable(new Name("b4"),s);
	LogicVariable b5=new LogicVariable(new Name("b5"),s);
	LogicVariable b6=new LogicVariable(new Name("b6"),s);
	LogicVariable b7=new LogicVariable(new Name("b7"),s);

	TermFactory tf = TacletForTests.services().getTermFactory();
	
	Term t_b1=tf.createTerm(Equality.EQUALS,
		                tf.createTerm(b1),
		                tf.createTerm(b1));
	Term t_b2=tf.createTerm(Equality.EQUALS,
		                tf.createTerm(b2),
		                tf.createTerm(b2));
	Term t_b3=tf.createTerm(Equality.EQUALS,
		                tf.createTerm(b3),
		                tf.createTerm(b3));
	Term t_b4=tf.createTerm(Equality.EQUALS,
		                tf.createTerm(b4),
		                tf.createTerm(b4));
	Term t_b5=tf.createTerm(Equality.EQUALS,
		                tf.createTerm(b5),
		                tf.createTerm(b5));
	Term t_b6=tf.createTerm(Equality.EQUALS,
		                tf.createTerm(b6),
		                tf.createTerm(b6));
	Term t_b7=tf.createTerm(Equality.EQUALS,
		                tf.createTerm(b7),
		                tf.createTerm(b7));

	Sequent s1=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
	    SequentFormula(t_b1)).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT); 
	Sequent s2=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
		SequentFormula(t_b2)).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT); 
	Sequent s3=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
		SequentFormula(t_b3)).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT); 
	Sequent s4=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
		SequentFormula(t_b4)).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT); 
	Sequent s5=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
		SequentFormula(t_b5)).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT); 
	Sequent s6=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
		SequentFormula(t_b6)).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT); 
	Sequent s7=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
		SequentFormula(t_b7)).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT); 

	p=new Proof("TestProofTree", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));

	n1=new Node(p, s1);
	n2=new Node(p, s2);
	n3=new Node(p, s3);
	n4=new Node(p, s4);
	n5=new Node(p, s5);
	n6=new Node(p, s6);
	n7=new Node(p, s7);

	n1.add(n2);
	n1.add(n3);
	n1.add(n4);
	n3.add(n5);
	n5.add(n6);
	n5.add(n7);

	p.setRoot(n1);
    }
    
    public void tearDown() {
        p = null;
        n1 = null;
        n2 = null;
        n3 = null;
        n4 = null;
        n5 = null;
        n6 = null;
        n7 = null;
    }

    
}