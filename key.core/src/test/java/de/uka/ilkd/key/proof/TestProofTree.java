/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * class tests the tree of proof
 */


public class TestProofTree {
    Proof p;
    Node n1;
    Node n2;
    Node n3;
    Node n4;
    Node n5;
    Node n6;
    Node n7;


    @BeforeEach
    public void setUp() {
        Sort s = new SortImpl(new Name("s"));
        LogicVariable b1 = new LogicVariable(new Name("b1"), s);
        LogicVariable b2 = new LogicVariable(new Name("b2"), s);
        LogicVariable b3 = new LogicVariable(new Name("b3"), s);
        LogicVariable b4 = new LogicVariable(new Name("b4"), s);
        LogicVariable b5 = new LogicVariable(new Name("b5"), s);
        LogicVariable b6 = new LogicVariable(new Name("b6"), s);
        LogicVariable b7 = new LogicVariable(new Name("b7"), s);

        TermFactory tf = TacletForTests.services().getTermFactory();

        Term t_b1 = tf.createTerm(Equality.EQUALS, tf.createTerm(b1), tf.createTerm(b1));
        Term t_b2 = tf.createTerm(Equality.EQUALS, tf.createTerm(b2), tf.createTerm(b2));
        Term t_b3 = tf.createTerm(Equality.EQUALS, tf.createTerm(b3), tf.createTerm(b3));
        Term t_b4 = tf.createTerm(Equality.EQUALS, tf.createTerm(b4), tf.createTerm(b4));
        Term t_b5 = tf.createTerm(Equality.EQUALS, tf.createTerm(b5), tf.createTerm(b5));
        Term t_b6 = tf.createTerm(Equality.EQUALS, tf.createTerm(b6), tf.createTerm(b6));
        Term t_b7 = tf.createTerm(Equality.EQUALS, tf.createTerm(b7), tf.createTerm(b7));

        Sequent s1 = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(t_b1)).semisequent(),
            Semisequent.EMPTY_SEMISEQUENT);
        Sequent s2 = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(t_b2)).semisequent(),
            Semisequent.EMPTY_SEMISEQUENT);
        Sequent s3 = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(t_b3)).semisequent(),
            Semisequent.EMPTY_SEMISEQUENT);
        Sequent s4 = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(t_b4)).semisequent(),
            Semisequent.EMPTY_SEMISEQUENT);
        Sequent s5 = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(t_b5)).semisequent(),
            Semisequent.EMPTY_SEMISEQUENT);
        Sequent s6 = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(t_b6)).semisequent(),
            Semisequent.EMPTY_SEMISEQUENT);
        Sequent s7 = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(t_b7)).semisequent(),
            Semisequent.EMPTY_SEMISEQUENT);

        p = new Proof("TestProofTree",
            new InitConfig(new Services(AbstractProfile.getDefaultProfile())));

        n1 = new Node(p, s1);
        n2 = new Node(p, s2);
        n3 = new Node(p, s3);
        n4 = new Node(p, s4);
        n5 = new Node(p, s5);
        n6 = new Node(p, s6);
        n7 = new Node(p, s7);

        n1.add(n2);
        n1.add(n3);
        n1.add(n4);
        n3.add(n5);
        n5.add(n6);
        n5.add(n7);

        p.setRoot(n1);
    }

    @AfterEach
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


    @Test
    public void testLeaves() {

        // test sanityCheck
        assertTrue(p.root().sanityCheckDoubleLinks(), "tree should have good sanity");

        assertEquals(-1, n1.siblingNr(), "Root has sibling nr -1");
        assertEquals(0, n2.siblingNr(), "n2 should have sibling nr 0");
        assertEquals(1, n3.siblingNr(), "n3 should have sibling nr 1");
        assertEquals(2, n4.siblingNr(), "n4 should have sibling nr 2");
        assertEquals(0, n5.siblingNr(), "n5 should have sibling nr 0");

        Iterator<Node> it = p.root().leavesIterator();
        int i = 0;
        while (it.hasNext()) {
            assertEquals(it.next().toString(), (new Node[] { n2, n6, n7, n4 })[i].toString());
            i++;
        }
        it = p.root().childrenIterator();

        i = 0;
        while (it.hasNext()) {
            assertEquals(it.next().toString(), (new Node[] { n2, n3, n4 })[i].toString());
            i++;
        }

        n3.remove();
        assertEquals(-1, n3.siblingNr(), "n3 is no longer a sibling and should have sibling nr -1");
        assertEquals(0, n2.siblingNr(), "n2 should have sibling nr 0");
        assertEquals(1, n4.siblingNr(), "n4 should have sibling nr 1");

        it = p.root().childrenIterator();
        i = 0;
        while (it.hasNext()) {
            assertEquals(it.next().toString(), (new Node[] { n2, n4 })[i].toString());
            i++;
        }

        n1.remove(n2);
        assertEquals(-1, n2.siblingNr(), "n2 is no longer a sibling and should have sibling nr -1");
        assertEquals(0, n4.siblingNr(), "n4 should have sibling nr 0");

        it = p.root().childrenIterator();
        i = 0;
        while (it.hasNext()) {
            assertEquals(it.next().toString(), (new Node[] { n4 })[i].toString());
            i++;
        }

        n1.remove(n4);
        assertEquals(-1, n4.siblingNr(), "n4 is no longer a sibling and should have sibling nr -1");
        assertEquals(0, n1.childrenCount());


    }


}
